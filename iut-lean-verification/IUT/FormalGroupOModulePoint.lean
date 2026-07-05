/-
  # M257F: 点集合上の O-加群構造の総括 capstone（柱C・O-加群構造の残件を 1 スライス）

  柱C（issue #37）。点集合 F(pℤ_p) 上の O-作用の代数則は、これまで三つの
  モジュールに分かれて確立してきた:

  * M231F（`FormalGroupPointLaws.lean`）— 点群法則: 単位・可換・逆元・
    ℤ_p-作用の加法性 F([a]x,[b]x)=[a+b]x・結合。
  * M247F（`FormalGroupPointOAction.lean`）— 環作用の乗法側: 単位作用
    [1]x=x・零作用 [0]x=0・乗法的合成 [a]([b]x)=[ab]x・加法性の再輸出。
  * M252F（`FormalGroupPointODerived.lean`）— 可換環的派生則: スカラー
    合成の可換 [a]([b]x)=[b]([a]x)・形式群加法のスカラー点上での可換
    F([a]x,[b]x)=F([b]x,[a]x)・スカラー負元による点逆元 F([a]x,[−a]x)=0。

  本層はこれら三つを**単一の総括レコード**に束ねて O-加群構造の点版を
  certification するとともに、M247F の乗法的合成 `lt_point_scalar_mul` と
  零作用 `lt_point_scalar_zero` から従う**新しい点等式 4 本**——単位
  スカラーの左作用・零スカラーの両側吸収・スカラー作用の結合律——を
  追加で機械検証して束ねる。分配律 [a](x+_F y)=[a]x+_F[a]y（M100F が
  tier-L 難度で対象外）は **honest limitation として明示的に除外**する。

  * M257F-1 `lt_point_scalar_one_left` — **単位スカラーの左作用（新）**
    [1]([a]x) = [a]x。M247F `lt_point_scalar_mul`（[1]([a]x)=[1·a]x）を
    ℤ_p の `one_mul`（1·a=a）で潰す。M247F-1（[1]x=x, 基点上）とは
    別の新しい点等式（スカラー点 [a]x 上での単位作用）。
  * M257F-2 `lt_point_scalar_zero_left` — **零スカラーの左吸収（新）**
    [0]([a]x) = 0。`lt_point_scalar_mul`（[0]([a]x)=[0·a]x）を
    `mul_comm`+`mul_zero`（0·a=a·0=0）で [0]x に潰し `lt_point_scalar_zero`
    で零へ。
  * M257F-3 `lt_point_scalar_zero_right` — **零スカラー点の右吸収（新）**
    [a]([0]x) = 0。`lt_point_scalar_mul`（[a]([0]x)=[a·0]x）を `mul_zero`
    （a·0=0）で [0]x に潰し `lt_point_scalar_zero` で零へ。
  * M257F-4 `lt_point_scalar_assoc` — **スカラー作用の結合律（新・本丸）**
    [a]([b]([c]x)) = [(a·b)·c]x。内側点 [c]x を基点として
    `lt_point_scalar_mul p hp a b`（[a]([b]([c]x))=[ab]([c]x)）を適用し、
    続けて `lt_point_scalar_mul p hp (ab) c`（[ab]([c]x)=[(ab)c]x）で
    合流する。二重ネストの可除性 witness は M79 `zpEval_closed` が自動
    供給する。M247F の生の合成 [a]([b]x)=[ab]x（一段）からは得られない
    **三段の新しい点等式**（O-加群作用の結合律の点版）。
  * M257F-5 `FormalGroupOModulePointData` /
    `formalGroupOModulePoint_exists` — 三モジュール（M231F/M247F/M252F）
    の総括データ束 + 新 4 則を単一レコードに束ねた certification と存在。

  ## 意義

  点集合 F(pℤ_p) 上の O-作用が備える代数則の総体——群法則（M231F）・
  環作用（M247F）・可換環的派生則（M252F）——を単一の型
  `FormalGroupOModulePointData` に固定し、さらにスカラー作用の結合律・
  単位左作用・零吸収という**これまで束ねられていなかった新しい点等式**を
  加えて、O-加群構造の点版の代数的一貫性を一段確かなものにする。M100F が
  級数レベルで閉じた O → End(F) の環準同型の点への忠実な輸送の総まとめ。

  ## 正直な限定

  * (1) 本 capstone は O-作用の**環準同型としての F-準同型性（分配律）**
    [a](x +_F y) = [a]x +_F [a]y（＝級数レベル [a](F(X,Y)) =
    F([a]X, [a]Y)）を**依然として扱わない**——これは M100F の正直申告
    でも End(F) 全射性と並んで対象外とされた別項目であり（2 変数一意性を
    要する tier-L 難度）、本層でも honest limitation として明示的に
    除外する。束ねるのはスカラー側（合成・可換・負元・結合・単位・零）の
    派生則のみ。
  * (2) 三モジュール（M231F/M247F/M252F）を同一パラメータ (p, hp) の下で
    単一レコードに**並べて**束ねるが、これらから「点集合が O-加群
    （あるいは O 上の加群）の型クラスインスタンスをなす」束縛
    （Mathlib 型クラスへの橋渡し）は与えない——点集合を担う単一の台型
    （subtype）を定義して群公理・加群公理を型クラスとして充足させる
    作業は各サブモジュールと同様に範囲外。
  * (3) 各点の可除性 witness は M247F/M231F と同一の `zpEval_closed`
    明示 witness を保持し、点集合上の一意表現への正規化は行わない。
  * (4) 新 4 則（M257F-1〜4）は M247F `lt_point_scalar_mul` /
    `lt_point_scalar_zero` と ℤ_p の環公理（`one_mul`/`mul_zero`/
    `mul_comm`）の合成であり、新規の級数レベル証明は導入しない
    （新しいのは**点等式の組み立て**——特に結合律 M257F-4 は二重ネスト
    の点等式で M247F 単体には無い）。既存 3 データ束の各フィールドは
    元の witness の直接再利用（新規証明ゼロ）。
  * 全て選択公理不使用（型継承除く）。`#print axioms` で実測。
    可能なら [propext, Quot.sound] のみ。
  * サブエージェント並行部品。
-/
import IUT.FormalGroupPointODerived
import IUT.FormalGroupPointLaws

namespace IUT

/-! ## M257F-1: 単位スカラーの左作用（新） -/

/-- **定理 (M257F-1): 単位スカラーの左作用** — [1]([a]x) = [a]x。
    M247F `lt_point_scalar_mul`（[1]([a]x) = [1·a]x）を ℤ_p の `one_mul`
    （1·a = a）で潰す。M247F-1（基点上の [1]x = x）とは別の新しい点
    等式（スカラー点 [a]x 上での単位作用）。 -/
theorem lt_point_scalar_one_left (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltSol p hp ((zpRing p).one))
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
    = zpEval p (ltSol p hp a) x e hx :=
  (lt_point_scalar_mul p hp ((zpRing p).one) a x e hx).trans
    (congrArg (fun c => zpEval p (ltSol p hp c) x e hx)
      ((zpRing p).one_mul a))

/-! ## M257F-2: 零スカラーの左吸収（新） -/

/-- **定理 (M257F-2): 零スカラーの左吸収** — [0]([a]x) = 0。
    `lt_point_scalar_mul`（[0]([a]x) = [0·a]x）を `mul_comm`+`mul_zero`
    （0·a = a·0 = 0）で [0]x に潰し、M247F `lt_point_scalar_zero` で
    零へ。 -/
theorem lt_point_scalar_zero_left (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltSol p hp ((zpRing p).zero))
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
    = (zpRing p).zero :=
  (lt_point_scalar_mul p hp ((zpRing p).zero) a x e hx).trans
    ((congrArg (fun c => zpEval p (ltSol p hp c) x e hx)
        (((zpRing p).mul_comm ((zpRing p).zero) a).trans
          (CRing.mul_zero (zpRing p) a))).trans
      (lt_point_scalar_zero p hp x e hx))

/-! ## M257F-3: 零スカラー点の右吸収（新） -/

/-- **定理 (M257F-3): 零スカラー点の右吸収** — [a]([0]x) = 0。
    `lt_point_scalar_mul`（[a]([0]x) = [a·0]x）を `mul_zero`（a·0 = 0）で
    [0]x に潰し、M247F `lt_point_scalar_zero` で零へ。 -/
theorem lt_point_scalar_zero_right (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltSol p hp a)
      (zpEval p (ltSol p hp ((zpRing p).zero)) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp ((zpRing p).zero)))
          x e hx))
      (zpEval_closed p hp.1 (ltSol p hp ((zpRing p).zero)) rfl x e hx)
    = (zpRing p).zero :=
  (lt_point_scalar_mul p hp a ((zpRing p).zero) x e hx).trans
    ((congrArg (fun c => zpEval p (ltSol p hp c) x e hx)
        (CRing.mul_zero (zpRing p) a)).trans
      (lt_point_scalar_zero p hp x e hx))

/-! ## M257F-4: スカラー作用の結合律（新・本丸） -/

/-- **定理 (M257F-4): スカラー作用の結合律（本丸）** —
    [a]([b]([c]x)) = [(a·b)·c]x。内側点 [c]x を基点として
    `lt_point_scalar_mul p hp a b`（[a]([b]([c]x)) = [ab]([c]x)）を適用し、
    続けて `lt_point_scalar_mul p hp (ab) c`（[ab]([c]x) = [(ab)c]x）で
    合流。二重ネストの可除性 witness は M79 `zpEval_closed` が自動供給。
    M247F の一段合成 [a]([b]x) = [ab]x からは得られない三段の新しい点
    等式（O-加群作用の結合律の点版）。 -/
theorem lt_point_scalar_assoc (p : Nat) (hp : IsPrime p)
    (a b c : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltSol p hp a)
      (zpEval p (ltSol p hp b)
        (zpEval p (ltSol p hp c) x e hx)
        ((zpRing p).mul e
          (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
        (zpEval_closed p hp.1 (ltSol p hp c) rfl x e hx))
      ((zpRing p).mul
        ((zpRing p).mul e
          (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
        (zpEval p (psShift (zpRing p) (ltSol p hp b))
          (zpEval p (ltSol p hp c) x e hx)
          ((zpRing p).mul e
            (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
          (zpEval_closed p hp.1 (ltSol p hp c) rfl x e hx)))
      (zpEval_closed p hp.1 (ltSol p hp b) rfl
        (zpEval p (ltSol p hp c) x e hx)
        ((zpRing p).mul e
          (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
        (zpEval_closed p hp.1 (ltSol p hp c) rfl x e hx))
    = zpEval p (ltSol p hp ((zpRing p).mul ((zpRing p).mul a b) c)) x e hx :=
  (lt_point_scalar_mul p hp a b
      (zpEval p (ltSol p hp c) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp c) rfl x e hx)).trans
    (lt_point_scalar_mul p hp ((zpRing p).mul a b) c x e hx)

/-! ## M257F-5: 総括 capstone -/

/-- **点集合上の O-加群構造の総括データ（M257F-5）**: 素数 p・
    `hp : IsPrime p` に対し、Lubin–Tate 形式群 F = lt2Sol p hp の点集合
    F(pℤ_p) 上の O-作用が備える代数則の総体を単一レコードに束ねる:
    群法則（M231F）・環作用（M247F）・可換環的派生則（M252F）の三データ束と、
    本層の新しい派生則（単位スカラー左作用・零スカラー両側吸収・スカラー
    作用の結合律）。分配律は honest limitation として除外（limitation (1)）。 -/
structure FormalGroupOModulePointData (p : Nat) (hp : IsPrime p) where
  /-- M231F: 点群法則（単位・可換・逆元・加群加法性・結合）。 -/
  groupLaws : FormalGroupPointLawsData p hp
  /-- M247F: 環作用（単位作用・零作用・乗法的合成・加法性）。 -/
  oAction : FormalGroupPointOActionData p hp
  /-- M252F: 可換環的派生則（合成可換・加法可換・スカラー負元逆元）。 -/
  oDerived : FormalGroupPointODerivedData p hp
  /-- M257F-1: 単位スカラーの左作用 [1]([a]x) = [a]x。 -/
  scalarOneLeft : ∀ (a x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval p (ltSol p hp ((zpRing p).one))
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
    = zpEval p (ltSol p hp a) x e hx
  /-- M257F-2: 零スカラーの左吸収 [0]([a]x) = 0。 -/
  scalarZeroLeft : ∀ (a x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval p (ltSol p hp ((zpRing p).zero))
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
    = (zpRing p).zero
  /-- M257F-3: 零スカラー点の右吸収 [a]([0]x) = 0。 -/
  scalarZeroRight : ∀ (a x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval p (ltSol p hp a)
      (zpEval p (ltSol p hp ((zpRing p).zero)) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp ((zpRing p).zero)))
          x e hx))
      (zpEval_closed p hp.1 (ltSol p hp ((zpRing p).zero)) rfl x e hx)
    = (zpRing p).zero
  /-- M257F-4: スカラー作用の結合律 [a]([b]([c]x)) = [(a·b)·c]x。 -/
  scalarAssoc : ∀ (a b c x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval p (ltSol p hp a)
      (zpEval p (ltSol p hp b)
        (zpEval p (ltSol p hp c) x e hx)
        ((zpRing p).mul e
          (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
        (zpEval_closed p hp.1 (ltSol p hp c) rfl x e hx))
      ((zpRing p).mul
        ((zpRing p).mul e
          (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
        (zpEval p (psShift (zpRing p) (ltSol p hp b))
          (zpEval p (ltSol p hp c) x e hx)
          ((zpRing p).mul e
            (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
          (zpEval_closed p hp.1 (ltSol p hp c) rfl x e hx)))
      (zpEval_closed p hp.1 (ltSol p hp b) rfl
        (zpEval p (ltSol p hp c) x e hx)
        ((zpRing p).mul e
          (zpEval p (psShift (zpRing p) (ltSol p hp c)) x e hx))
        (zpEval_closed p hp.1 (ltSol p hp c) rfl x e hx))
    = zpEval p (ltSol p hp ((zpRing p).mul ((zpRing p).mul a b) c)) x e hx

/-- **証人（M257F-5）**: 点集合 F(pℤ_p) 上の O-作用が群法則・環作用・
    可換環的派生則（三モジュールの直接再利用）と本層の新 4 則を実際に
    備える。 -/
def formalGroupOModulePointData (p : Nat) (hp : IsPrime p) :
    FormalGroupOModulePointData p hp where
  groupLaws := formalGroupPointLawsData p hp
  oAction := formalGroupPointOActionData p hp
  oDerived := formalGroupPointODerivedData p hp
  scalarOneLeft := lt_point_scalar_one_left p hp
  scalarZeroLeft := lt_point_scalar_zero_left p hp
  scalarZeroRight := lt_point_scalar_zero_right p hp
  scalarAssoc := lt_point_scalar_assoc p hp

/-- **capstone (M257F-5): 存在** — 柱C 形式群 F = lt2Sol p hp の点集合
    F(pℤ_p) 上の O-加群構造（群法則・環作用・可換環的派生則の総体 +
    単位左作用・零両側吸収・スカラー結合律の新則）が無矛盾に存在する。
    分配律を honest limitation として除いた、O-加群構造の点版の総まとめ。 -/
theorem formalGroupOModulePoint_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (FormalGroupOModulePointData p hp) :=
  ⟨formalGroupOModulePointData p hp⟩

end IUT
