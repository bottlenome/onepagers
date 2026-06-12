/-
  IUT/RamifiedEntrance.lean — M85F（分岐 LCFT 入口の総括:
  M79F/M81F/M82F/M83F/M84F の合流インターフェース）

  分岐 LCFT への入口の物語が完結した: 基底 ℤ_p では πⁿ-捻れ点は
  自明（M81F）、分岐拡大 O = ℤ_p[[X]]/(X^{p−1} + π) には非自明な
  捻れ点 λ が存在し（M82F/M83F）、その Teichmüller 共役族 {ω(a)λ}
  は p−1 個の相異なる非自明 [π]-捻れ点を与える（M84F）。本ファイルは
  これらを **単一の機械検証インターフェース** に束ね、ダッシュボードが
  一つの定理を指せるようにする（LocalCFTData / FormalOModuleData と
  同じ「構造 + witness」の家風）。

  * M85F-1 `RamifiedEntranceData` — 入口データの構造化:
    (i) 基底の自明性（M81F-6 torsion_trivial）、
    (ii) 拡大環 ext・構造射 extOf・一意化元 lam と
         非自明性 1 ≠ 0（M82F-8）・λ ≠ 0（M83F-6）・
         Eisenstein 関係 λ^{p−1} = −π（M82F-5）、
    (iii) f-作用 extF・[πⁿ]-作用 extIter と
          捻れ性 [πⁿ]λ = 0（M83F-5）・基底作用との両立（M83F-7）、
    (iv) 共役族 family a = ω(a)λ の捻れ性・非自明性・相異性
         （M84F-8a/8b）
  * M85F-2 `ramifiedEntrance` — witness: ext := eisRing、
    extOf := eisOf、lam := eisLambda、extF := eisF、
    extIter := eisIter、family := a ↦ ω(a)λ。全フィールドは既存定理の
    記録のみ（hp.1 : 2 ≤ p の受け渡しと ∧ の射影だけの純粋な梱包）
  * M85F-3 `ramified_entrance_exists` — 見出し定理:
    Nonempty (RamifiedEntranceData p hp hodd)
  * M85F-4 `ramified_entrance_count` — 易しいストレッチ:
    witness の族の相異性の言い換え（族は本当に p−1 個ある）

  Λ₁ の上界（ちょうど p 点であること）・O の整域性・Galois 作用・
  rec の分岐成分は未形式化 — 本構造はそれらの定式化の土台となる
  インターフェース。p = 2 の除外（hodd : 3 ≤ p）は λ ≠ 0 が
  M83F-6 の係数比較に依存するため（同じ正直申告）。
  全て選択公理不使用。
-/
import IUT.EisensteinConjugates

namespace IUT

/-! ## 分岐入口データのインターフェース -/

/-- **M85F-1: 分岐 LCFT 入口データ** — 基底の捻れ自明性・分岐拡大の
    骨格（環・構造射・一意化元・Eisenstein 関係）・[πⁿ]-作用と
    基底作用の両立・p−1 個の相異なる非自明共役捻れ点族を一括に束ねる
    インターフェース構造。 -/
structure RamifiedEntranceData (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) where
  /-- 基底 ℤ_p では πⁿ-捻れ点は自明（M81F-6）。 -/
  base_trivial : ∀ (n : Nat) (x e : (Zp p).carrier)
      (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
      IsTorsionPoint p n x e hx → x = (zpRing p).zero
  /-- 分岐拡大環 O。 -/
  ext : CRing
  /-- 構造射 ℤ_p → O。 -/
  extOf : RingHom (zpRing p) ext
  /-- 一意化元 λ ∈ O。 -/
  lam : ext.carrier
  /-- O は自明環でない（M82F-8）。 -/
  ext_nontrivial : ext.one ≠ ext.zero
  /-- λ ≠ 0（捻れの非自明性、M83F-6）。 -/
  lam_ne_zero : lam ≠ ext.zero
  /-- Eisenstein 関係 λ^{p−1} = −π（M82F-5）。 -/
  lam_eis : rpow ext lam (p - 1)
      = ext.neg (extOf.map ((toZp p).map ((p : Nat) : Int)))
  /-- O 上の f-作用。 -/
  extF : ext.carrier → ext.carrier
  /-- O 上の [πⁿ]-作用。 -/
  extIter : Nat → ext.carrier → ext.carrier
  /-- λ は全ての [πⁿ]（n ≥ 1）で消える捻れ点（M83F-5）。 -/
  lam_torsion : ∀ n, 1 ≤ n → extIter n lam = ext.zero
  /-- 構造射は基底の f-作用と O の f-作用を絡み合わせる（M83F-7）。 -/
  action_compat : ∀ (x e : (Zp p).carrier)
      (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
      extOf.map (zpEval p (ltPoly p) x e hx) = extF (extOf.map x)
  /-- 共役点族 a ↦ ω(a)·λ。 -/
  family : Nat → ext.carrier
  /-- 各 1 ≤ a < p で ω(a)λ は [π]-捻れ点（M84F-8a）。 -/
  family_torsion : ∀ a : Nat, 1 ≤ a → a < p →
      extIter 1 (family a) = ext.zero
  /-- 各 1 ≤ a < p で ω(a)λ ≠ 0（M84F-8a）。 -/
  family_ne_zero : ∀ a : Nat, 1 ≤ a → a < p → family a ≠ ext.zero
  /-- 1 ≤ a < b < p で ω(a)λ ≠ ω(b)λ（相異性、M84F-8b）。 -/
  family_distinct : ∀ a b : Nat, 1 ≤ a → a < b → b < p →
      family a ≠ family b

/-! ## witness: Eisenstein 拡大による充足 -/

/-- **M85F-2: witness** — O := eisRing、構造射 := eisOf、λ := eisLambda、
    f-作用 := eisF、[πⁿ]-作用 := eisIter、族 := a ↦ ω(a)λ が
    入口インターフェースを完全証明で充足する。全フィールドは
    M81F/M82F/M83F/M84F の既存定理の記録（公理化なし・新規数学なし）。 -/
def ramifiedEntrance (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    RamifiedEntranceData p hp hodd where
  base_trivial := torsion_trivial p hp hodd
  ext := eisRing p
  extOf := eisOf p
  lam := eisLambda p
  ext_nontrivial := eis_one_ne_zero p hp.1
  lam_ne_zero := eis_lambda_ne_zero p hodd
  lam_eis := eis_lambda_pow p hp.1
  extF := eisF p
  extIter := eisIter p
  lam_torsion := lambda_all_torsion p hp.1
  action_compat := eisOf_compat_f p hp.1
  family := fun a =>
    (eisRing p).mul ((eisOf p).map (teich p hp (a : Int))) (eisLambda p)
  family_torsion := fun a h1 h2 =>
    (lambda_one_torsion_family p hp hodd a h1 h2).1
  family_ne_zero := fun a h1 h2 =>
    (lambda_one_torsion_family p hp hodd a h1 h2).2
  family_distinct := lambda_one_family_distinct p hp hodd

/-! ## 見出し定理 -/

/-- **定理 (M85F-3): 分岐入口の存在** — 奇素数 p に対し分岐 LCFT
    入口データが存在する（witness は M85F-2、選択公理不使用）。 -/
theorem ramified_entrance_exists (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) : Nonempty (RamifiedEntranceData p hp hodd) :=
  ⟨ramifiedEntrance p hp hodd⟩

/-- **M85F-4: 族の個数の言い換え**（易しいストレッチ）— witness の
    共役族は 1 ≤ a < b < p で相異なる: Λ₁ は 0 と合わせて少なくとも
    p 点を含む（下界の再掲、M84F-8b の直接の言い換え）。 -/
theorem ramified_entrance_count (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) : ∀ a b : Nat, 1 ≤ a → a < b → b < p →
    (ramifiedEntrance p hp hodd).family a
      ≠ (ramifiedEntrance p hp hodd).family b :=
  (ramifiedEntrance p hp hodd).family_distinct

end IUT
