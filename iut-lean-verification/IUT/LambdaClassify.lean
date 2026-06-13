/-
  IUT/LambdaClassify.lean — M97F（柱B capstone: Λ₁ と自己準同型の
  完全分類の組み立て）

  材料は全て揃った: M84F は p−1 個の相異なる共役点 ω(a)λ（1 ≤ a < p）
  を構成し、M90F は NoZeroDiv の下で Λ₁ の元を 0 か Eisenstein 根
  t^{p−1} = −π に分類し、M95 は ℤ_p-固定自己準同型 σ について
  σ(λ) ≠ 0 なら σ(λ) が Eisenstein 根であることを示し、M96 は
  **根の個数 ≤ p−1**（因数定理）を完全証明した。本ファイルはこれらを
  組み立てる: Eisenstein 根 t が共役族 {ω(a)λ} を全て避けるなら、
  t と族で p 個の相異なる根ができて M96 に矛盾する。よって
  **Λ₁ ⊆ {0} ∪ {ω(a)λ}**・**σ(λ) は族に合流**（σ(λ) = ω(a)λ 型の
  分類）が ¬∀≠ 形で閉じる。

  * M97F-0 `lamFamily` / `rootSeq` / `rootSeq_lt` / `rootSeq_ge` —
    共役族 ω(a)λ の略記と、族 + 候補 t を 1 本に束ねる指示関数
    r(i) = ω(i+1)λ（i < p−1）/ t（i = p−1）。if-then-else は
    Nat.decLt による決定的な場合分け（選択公理不使用）
  * M97F-1 `eis_root_meets_family` — **本丸 1**: t^{p−1} = −π なる
    t は共役族を避けられない。避けたとすると rootSeq が p 個の
    相異なる Eisenstein 根（相異性 = M84F-8b + 回避仮定、根である
    こと = M90F-5 + 仮定）となり M96-7 eis_roots_bound に矛盾
  * M97F-2 `eis_torsion_classify_full` — **本丸 2**: t ∈ Λ₁ なら
    t = 0 ∨ ¬(t が族を避ける)。M90F-3 の二分が hD から直接出る
    ので排中律不要
  * M97F-3 `endo_lambda_meets_family` — **本丸 3**: ℤ_p-固定
    自己準同型 σ で σ(λ) ≠ 0 なら σ(λ) は族に合流（M95-4b + 本丸 1）。
    古典的な「σ(λ) = ω(a)λ」の構成的 ¬∀≠ 形
  * M97F-4 `eis_root_meets_family_dn` — **二重否定付き存在形**:
    ¬¬∃ a, t = ω(a)λ。¬∀¬ ⟺ ¬¬∃ は直観主義的に成立するので
    無料で従う。**正の ∃ 形（∃ a, t = ω(a)λ）は O の等値判定
    （逆極限の全レベルでの判定 = 決定不能）を要するため選択公理
    なしでは導けない — ¬∀≠ / ¬¬∃ 形が本層の正直な成果物**
  * M97F-5 `LambdaClassifyData` / `lambdaClassify` /
    `lambdaClassify_exists` — 総括: 族が根であること（M90F-5）・
    相異性（M84F-8b）・本丸 1–3 を束ねた純レコードと witness・
    Nonempty ヘッドライン

  NoZeroDiv (eisRing p) は仮定として受け取る（witness 付き整域性は
  M93F/M96F が別経路で整備中）。p = 2 の除外（hodd : 3 ≤ p）は
  λ ≠ 0 が M83F-6 の係数比較に依存するため（既存層と同じ正直申告）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.FactorTheorem
import IUT.EisEndoRigidity

namespace IUT

/-! ## 共役族の略記と指示関数 -/

/-- **M97F-0a: 共役族の略記** — ω(a)·λ（a : Nat、p ∤ a のとき
    非自明な共役点）。 -/
def lamFamily (p : Nat) (hp : IsPrime p) (a : Nat) :
    (eisRing p).carrier :=
  (eisRing p).mul ((eisOf p).map (teich p hp (a : Int))) (eisLambda p)

/-- **M97F-0b: 指示関数** — r(i) = ω(i+1)λ（i < p−1）/ t（それ以外）。
    Nat.decLt による if-then-else（選択公理不使用）。 -/
def rootSeq (p : Nat) (hp : IsPrime p) (t : (eisRing p).carrier)
    (i : Nat) : (eisRing p).carrier :=
  if i < p - 1 then lamFamily p hp (i + 1) else t

/-- **M97F-0c: 指示関数の値（族側）**。 -/
theorem rootSeq_lt (p : Nat) (hp : IsPrime p) (t : (eisRing p).carrier)
    (i : Nat) (h : i < p - 1) :
    rootSeq p hp t i = lamFamily p hp (i + 1) := by
  show (if i < p - 1 then lamFamily p hp (i + 1) else t)
    = lamFamily p hp (i + 1)
  exact if_pos h

/-- **M97F-0d: 指示関数の値（候補側）**。 -/
theorem rootSeq_ge (p : Nat) (hp : IsPrime p) (t : (eisRing p).carrier)
    (i : Nat) (h : ¬ i < p - 1) : rootSeq p hp t i = t := by
  show (if i < p - 1 then lamFamily p hp (i + 1) else t) = t
  exact if_neg h

/-! ## 本丸 1: Eisenstein 根は共役族を避けられない -/

/-- **定理 (M97F-1): Eisenstein 根は族に合流する（本丸 1）** —
    t^{p−1} = −π なる t が全ての ω(a)λ（1 ≤ a < p）と異なることは
    ありえない。避けたとすると rootSeq p hp t が p 個（添字 0..p−1）の
    相異なる根: 族内の相異性は M84F-8b（添字をずらして 1 ≤ i+1 <
    j+1 < p）、族と t の相異性は回避仮定、根であることは M90F-5
    （族、無条件）と仮定 ht（t）。これは M96-7 eis_roots_bound
    （根の個数 ≤ p−1）に矛盾。 -/
theorem eis_root_meets_family (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p)) (t : (eisRing p).carrier)
    (ht : rpow (eisRing p) t (p - 1)
      = (eisRing p).neg
          ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))) :
    ¬ (∀ a : Nat, 1 ≤ a → a < p → t ≠ lamFamily p hp a) := by
  intro hav
  refine eis_roots_bound p hodd hD (rootSeq p hp t) ?_ ?_
  · -- 相異性: i < j ≤ p−1 で rootSeq i ≠ rootSeq j
    intro i j hij hj
    cases Nat.lt_or_ge j (p - 1) with
    | inl hjlt =>
      -- 両方とも族内: M84F-8b（1 ≤ i+1 < j+1 < p）
      rw [rootSeq_lt p hp t i (by omega), rootSeq_lt p hp t j hjlt]
      exact lambda_one_family_distinct p hp hodd (i + 1) (j + 1)
        (by omega) (by omega) (by omega)
    | inr hjge =>
      -- j = p−1: rootSeq j = t、rootSeq i は族内 — 回避仮定で相異
      rw [rootSeq_lt p hp t i (by omega), rootSeq_ge p hp t j (by omega)]
      intro h
      exact hav (i + 1) (by omega) (by omega) h.symm
  · -- 根であること: i ≤ p−1 で rootSeq i ^{p−1} = −π
    intro i hi
    cases Nat.lt_or_ge i (p - 1) with
    | inl hilt =>
      rw [rootSeq_lt p hp t i hilt]
      exact conj_eis_equation p hp
        (nat_lt_not_dvd_int p (i + 1) (by omega) (by omega))
    | inr hige =>
      rw [rootSeq_ge p hp t i (by omega)]
      exact ht

/-! ## 本丸 2: Λ₁ の完全分類（¬∀≠ 形） -/

/-- **定理 (M97F-2): Λ₁ の完全分類（本丸 2）** — NoZeroDiv の下で
    t ∈ Λ₁ なら t = 0 または t は共役族を避けられない（古典的には
    Λ₁ = {0} ∪ {ω(a)λ : 1 ≤ a < p}）。M90F-3 の二分（hD から直接
    出る — 排中律不要）の第二枝に M97F-1 を合成。 -/
theorem eis_torsion_classify_full (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) (hD : NoZeroDiv (eisRing p))
    (t : (eisRing p).carrier) (ht : IsEisTorsion p 1 t) :
    t = (eisRing p).zero
      ∨ ¬ (∀ a : Nat, 1 ≤ a → a < p → t ≠ lamFamily p hp a) := by
  cases eisTorsion_one_classify p hp.1 hD ht with
  | inl h0 => exact Or.inl h0
  | inr hroot => exact Or.inr (eis_root_meets_family p hp hodd hD t hroot)

/-! ## 本丸 3: 自己準同型の分類（σ(λ) は族に合流） -/

/-- **定理 (M97F-3): σ(λ) は族に合流（本丸 3）** — ℤ_p の像を固定
    する任意の環自己準同型 σ で σ(λ) ≠ 0 なら、σ(λ) は共役族を
    避けられない。M95-4b（σ(λ) は Eisenstein 根）+ M97F-1。古典的な
    「σ(λ) = ω(a)λ（ある a）」の構成的 ¬∀≠ 形。 -/
theorem endo_lambda_meets_family (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) (hD : NoZeroDiv (eisRing p))
    (σ : RingHom (eisRing p) (eisRing p))
    (hfix : ∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z)
    (hne : σ.map (eisLambda p) ≠ (eisRing p).zero) :
    ¬ (∀ a : Nat, 1 ≤ a → a < p →
      σ.map (eisLambda p) ≠ lamFamily p hp a) :=
  eis_root_meets_family p hp hodd hD (σ.map (eisLambda p))
    (endo_lambda_root p hp.1 hD σ hfix hne)

/-! ## 二重否定付き存在形（正直申告付き） -/

/-- **定理 (M97F-4): 二重否定付き存在形** — ¬∀¬ ⟺ ¬¬∃ は直観主義的
    同値なので、M97F-1 から ¬¬∃ a, t = ω(a)λ が無料で従う。
    正の ∃ 形は O（逆極限）の等値判定を要し選択公理なしでは
    導けない — 本層の正直な成果物は ¬∀≠ / ¬¬∃ 形。 -/
theorem eis_root_meets_family_dn (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) (hD : NoZeroDiv (eisRing p))
    (t : (eisRing p).carrier)
    (ht : rpow (eisRing p) t (p - 1)
      = (eisRing p).neg
          ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))) :
    ¬ ¬ ∃ a : Nat, 1 ≤ a ∧ a < p ∧ t = lamFamily p hp a := by
  intro hno
  exact eis_root_meets_family p hp hodd hD t ht
    (fun a h1 h2 heq => hno ⟨a, h1, h2, heq⟩)

/-! ## 総括: Λ₁ と自己準同型の完全分類データ -/

/-- **M97F-5a: 完全分類データ** — NoZeroDiv (eisRing p) の下での
    柱B 分類の全簿記: 共役族が Eisenstein 根であること（M90F-5）・
    族の相異性（M84F-8b）・Eisenstein 根の族への合流（M97F-1）・
    Λ₁ の完全分類（M97F-2）・自己準同型の分類（M97F-3）。 -/
structure LambdaClassifyData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p)) where
  /-- 共役族は Eisenstein 根: (ω(a)λ)^{p−1} = −π（1 ≤ a < p、無条件）。 -/
  conj_root : ∀ a : Nat, 1 ≤ a → a < p →
    rpow (eisRing p) (lamFamily p hp a) (p - 1)
      = (eisRing p).neg ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
  /-- 族の相異性: ω(a)λ ≠ ω(b)λ（1 ≤ a < b < p）。 -/
  family_distinct : ∀ a b : Nat, 1 ≤ a → a < b → b < p →
    lamFamily p hp a ≠ lamFamily p hp b
  /-- Eisenstein 根は族に合流: t^{p−1} = −π なら t は族を避けられない。 -/
  root_meets : ∀ t : (eisRing p).carrier,
    rpow (eisRing p) t (p - 1)
      = (eisRing p).neg ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) →
    ¬ (∀ a : Nat, 1 ≤ a → a < p → t ≠ lamFamily p hp a)
  /-- Λ₁ の完全分類: t ∈ Λ₁ なら t = 0 ∨ t は族に合流。 -/
  torsion_classify : ∀ t : (eisRing p).carrier, IsEisTorsion p 1 t →
    t = (eisRing p).zero
      ∨ ¬ (∀ a : Nat, 1 ≤ a → a < p → t ≠ lamFamily p hp a)
  /-- 自己準同型の分類: ℤ_p-固定 σ で σ(λ) ≠ 0 なら σ(λ) は族に合流。 -/
  endo_meets : ∀ σ : RingHom (eisRing p) (eisRing p),
    (∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) →
    σ.map (eisLambda p) ≠ (eisRing p).zero →
    ¬ (∀ a : Nat, 1 ≤ a → a < p →
      σ.map (eisLambda p) ≠ lamFamily p hp a)

/-- **M97F-5b: witness 本体** — M90F-5 + M84F-8b + M97F-1/2/3 が
    完全分類データを成す（純レコード、選択公理不使用）。 -/
def lambdaClassify (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p)) : LambdaClassifyData p hp hodd hD where
  conj_root := fun a h1 h2 =>
    conj_eis_equation p hp (nat_lt_not_dvd_int p a h1 h2)
  family_distinct := fun a b h1 h2 h3 =>
    lambda_one_family_distinct p hp hodd a b h1 h2 h3
  root_meets := fun t ht => eis_root_meets_family p hp hodd hD t ht
  torsion_classify := fun t ht =>
    eis_torsion_classify_full p hp hodd hD t ht
  endo_meets := fun σ hfix hne =>
    endo_lambda_meets_family p hp hodd hD σ hfix hne

/-- **定理 (M97F-5c): 完全分類の存在（ヘッドライン）** — O に零因子が
    なければ、Λ₁ は 0 と共役族 {ω(a)λ} で尽くされ（¬∀≠ 形）、
    ℤ_p-固定自己準同型の λ の行き先も 0 でなければ族に合流する。
    柱B の分類（組み立て段）完了。 -/
theorem lambdaClassify_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p)) :
    Nonempty (LambdaClassifyData p hp hodd hD) :=
  ⟨lambdaClassify p hp hodd hD⟩

end IUT
