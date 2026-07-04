/-
# M218F: 分岐 rec の合同全射性（柱B B-2 全射側・並行部品）

M197F（`RecRamifiedSurj`: K^× = p^ℤ × ℤ_p^× の貼り合わせのうち **単数側
O^× = ℤ_p^×** の被覆——各抽象骨格 σ_a を本物の単数 ω(a) で実現し、その
K^× 元 x = (0, ω(a)) の不分岐成分を自明にして分岐成分を σ_a に一致させた）
と M207F（`RecUnramified`: **付値・不分岐側** ⟨π⟩ = p^ℤ の被覆——k ↦ (k, 1)
で不分岐成分を toZhat(k) = Frobenius^k にし分岐成分を自明にした）を、
**両因子を同時に非自明に実現する合流スライス**へ束ねる。すなわち issue #36
（柱B B-2 残件）の「分岐 rec の全射性」を、K^× = p^ℤ × ℤ_p^× の直積像が
**不分岐目標 Frobenius^k と分岐目標 σ_a の任意の組を同時に掴む（joint 全射・
被覆）** という形で閉じる。

鍵となる観測: K^× 元を x = (k, ω(a))（付値 k、単数部は Teichmüller 代表
ω(a)）と取ると、貼り合わせ写像 `recLevelOne` は
  - **不分岐成分** = toZhat(k) = Frobenius^k（M207F の付値側被覆・k で任意）、
  - **分岐成分** = recInertia(ω(a)) = σ_a（M197F-2 `recInertia_teich_eq`
    の単数側被覆・a で任意）
へ同時に送る。M197F（x = (0, ω(a))）と M207F（x = (k, 1)）はそれぞれ一方の
因子だけを非自明にしていたが、**両方を独立パラメタ (k, a) として合流**させ
れば、貼り合わせ像は直積 {Frobenius^k} × {σ_a} を**残らず被覆**する。付値部
については各有限レベル ℤ/n の Frobenius 類が付値 k の適当な代表で被覆される
（Frobenius 稠密性、M207F-4 の合流版）ことも同時に閉じる。

  * M218F-1 `recJoint_covers` — **joint 被覆（本丸）**: 任意の付値 k と
    任意の剰余 a（p ∤ a）に対し、**不分岐成分が toZhat(k)（Frobenius^k）
    かつ分岐成分が σ_a** な K^× 元 x = (k, ω(a)) が存在（M207F 付値側 +
    M197F 単数側の合流）
  * M218F-2 `recJoint_level_covers` — **有限レベル joint 被覆**: 各有限
    レベル ℤ/n の任意の Frobenius 類 c と任意の剰余 a に対し、不分岐成分の
    n-射影が c・分岐成分が σ_a な K^× 元が存在（`Quot.exists_rep` +
    `limitProj` + M197F-2）
  * M218F-3 `RecSurjectiveData` / `recSurjectiveData` /
    `recSurjective_exists` — 総括レコード（合流実現子・不分岐 = toZhat(k)・
    分岐 = σ_a・各有限レベル joint 被覆・剰余上の忠実性）と witness・存在

意義: M197F は単数側（分岐成分 σ_a を実現・不分岐自明）、M207F は付値側
（不分岐成分 Frobenius^k を実現・分岐自明）をそれぞれ独立に閉じたが、
「両因子を**同時に**任意目標へ合わせられる（貼り合わせ像が直積 {Frobenius^k}
× {σ_a} を被覆する）」という joint 全射性は未接続だった。本層は x = (k, ω(a))
という単一の K^× 元で両側被覆を同時実現し、M197F+M207F を直積の全射性へ
統合する。各有限レベルでも同様に joint 被覆が成り立ち、剰余上の忠実性
（M87F-4 `eisGal_faithful`）で単数側は (ℤ/p)^× 上の全単射となる。

正直な限定: 本層が閉じるのは **貼り合わせ像 K^× → ẑ × End(O) が直積
{Frobenius^k : k ∈ ℤ} × {σ_a : p ∤ a} を被覆する joint 全射性** のスライス
のみ。**ẑ 全体への位相的全射**（toZhat の像 ℤ は ẑ で稠密だが全射ではない
——M13-8 `toZhat_injective` 単射性の裏返し・不分岐側の閉包全体は掴めない）、
分岐 rec の**完全な抽象全射性**（{σ_a} が抽象 Galois 群 Aut(O) 全体と一致
すること）、および **Λₙ(n ≥ 2) への作用**（塔 O_n 版の rec）は次層に残る
（issue #36 の残余）。全て選択公理不使用（M197F/M207F/M94 から propext,
Quot.sound を継承、新規 Classical.choice なし）。サブエージェント並行部品。
-/
import IUT.RecRamifiedSurj
import IUT.RecUnramified

namespace IUT

/-! ## M218F-1: joint 被覆（本丸）— 不分岐 Frobenius^k と分岐 σ_a を同時実現 -/

/-- **定理 (M218F-1): joint 被覆（本丸）** — 任意の付値 k ∈ ℤ と任意の
    剰余 a（p ∤ a）に対し、貼り合わせ相互作用 `recLevelOne` の像が
    **不分岐目標 toZhat(k)（= Frobenius^k）と分岐目標 σ_a を同時に掴む**
    K^× 元 x = (k, ω(a)) ∈ p^ℤ × ℤ_p^× が存在する。M207F-3
    `recUnram_covers`（付値側・分岐自明）と M197F-4 `recRamSurj_covers`
    （単数側・不分岐自明）の**合流**——独立パラメタ (k, a) で両因子を同時に
    非自明実現する、貼り合わせ像の直積被覆（joint 全射性）のヘッドライン。 -/
theorem recJoint_covers (p : Nat) (hp : IsPrime p) (k : Int) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    ∃ x : (QpUnits p hp).carrier,
      (recLevelOne p hp x).1 = toZhat.map k ∧
      ∀ t, (recLevelOne p hp x).2.map t = (eisGal p hp a ha).map t := by
  refine ⟨(k, ⟨teich p hp a, isZpUnit_teich p hp ha⟩), rfl, ?_⟩
  intro t
  exact recInertia_teich_eq p hp ha t

/-! ## M218F-2: 有限レベル joint 被覆 -/

/-- **定理 (M218F-2): 有限レベル joint 被覆** — 各有限レベル ℤ/n の任意の
    Frobenius 類 c と任意の剰余 a（p ∤ a）に対し、**不分岐成分の n-射影が
    c・分岐成分が σ_a** な K^× 元 x = (k, ω(a))（k は c の代表）が存在する。
    M207F-4 `recUnram_level_covers`（付値側の各有限レベル被覆・分岐自明）に
    M197F-2 `recInertia_teich_eq`（分岐 σ_a）を合流させた、有限レベルでの
    joint 全射性。ẑ 全体への全射は成り立たない（正直な限定）。 -/
theorem recJoint_level_covers (p : Nat) (hp : IsPrime p) (n : Nat)
    (c : (zmod n).carrier) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    ∃ x : (QpUnits p hp).carrier,
      (limitProj zmodSystem n).map (recLevelOne p hp x).1 = c ∧
      ∀ t, (recLevelOne p hp x).2.map t = (eisGal p hp a ha).map t := by
  obtain ⟨k, hk⟩ := Quot.exists_rep c
  refine ⟨(k, ⟨teich p hp a, isZpUnit_teich p hp ha⟩), ?_, ?_⟩
  · show (limitProj zmodSystem n).map (toZhat.map k) = c
    rw [show (limitProj zmodSystem n).map (toZhat.map k)
        = Quot.mk (modCong n).rel k from rfl, hk]
  · intro t
    exact recInertia_teich_eq p hp ha t

/-! ## M218F-3: 総括 -/

/-- **M218F-3a: 分岐 rec の joint 全射（被覆）データ** — 付値 k と剰余 a を
    同時に実現する K^× 元（= (k, ω(a))）、その不分岐成分が toZhat(k) =
    Frobenius^k に一致すること（付値側被覆・M207F）、分岐成分が σ_a に一致
    すること（単数側被覆・M197F）、各有限レベルでの joint 被覆、および剰余
    上の忠実性（p ∤ (a − b) なら σ_a(λ) ≠ σ_b(λ)）を束ねる純レコード。
    M197F-5 `RecRamifiedSurjData`（単数側）と M207F-5 `RecUnramifiedData`
    （付値側）の合流。 -/
structure RecSurjectiveData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) where
  /-- 付値 k と剰余 a を同時に実現する K^× 元 = (k, ω(a))。 -/
  realize : Int → (a : Int) → ¬ ((p : Nat) : Int) ∣ a → (QpUnits p hp).carrier
  /-- 付値側被覆: 実現子の不分岐成分は Frobenius^k = toZhat(k) に一致。 -/
  realize_unram : ∀ (k a : Int) (ha : ¬ ((p : Nat) : Int) ∣ a),
    (recLevelOne p hp (realize k a ha)).1 = toZhat.map k
  /-- 単数側被覆: 実現子の分岐成分は抽象骨格 σ_a に完全一致。 -/
  realize_ram : ∀ (k a : Int) (ha : ¬ ((p : Nat) : Int) ∣ a) t,
    (recLevelOne p hp (realize k a ha)).2.map t = (eisGal p hp a ha).map t
  /-- 各有限レベル joint 被覆: ℤ/n の任意の Frobenius 類 c と任意の剰余 a は
      不分岐 n-射影が c・分岐が σ_a な K^× 元で同時に被覆される。 -/
  realize_level : ∀ (n : Nat) (c : (zmod n).carrier) (a : Int)
    (ha : ¬ ((p : Nat) : Int) ∣ a),
    ∃ x : (QpUnits p hp).carrier,
      (limitProj zmodSystem n).map (recLevelOne p hp x).1 = c ∧
      ∀ t, (recLevelOne p hp x).2.map t = (eisGal p hp a ha).map t
  /-- 忠実性: p ∤ (a − b) なら σ_a(λ) ≠ σ_b(λ)（被覆は剰余で単射）。 -/
  faithful : ∀ {a b : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hb : ¬ ((p : Nat) : Int) ∣ b), ¬ ((p : Nat) : Int) ∣ (a - b) →
    (eisGal p hp a ha).map (eisLambda p)
      ≠ (eisGal p hp b hb).map (eisLambda p)

set_option linter.unusedVariables false in
/-- **M218F-3b: witness** — 合流実現子を (k, a) ↦ (k, ω(a)) とし、M218F-1〜2
    + M197F-2 `recInertia_teich_eq` + M87F-4 `eisGal_faithful` で純レコードを
    充填（選択公理不使用）。 -/
def recSurjectiveData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    RecSurjectiveData p hp hodd where
  realize := fun k a ha => (k, ⟨teich p hp a, isZpUnit_teich p hp ha⟩)
  realize_unram := fun _ _ _ => rfl
  realize_ram := fun _ a ha => recInertia_teich_eq p hp ha
  realize_level := fun n c a ha => recJoint_level_covers p hp n c ha
  faithful := fun ha hb hab => eisGal_faithful p hp hodd ha hb hab

/-- **M218F-3c: 存在定理（ヘッドライン）** — 分岐 rec の貼り合わせ像は、
    単一の K^× 元 x = (k, ω(a)) で不分岐目標 Frobenius^k と分岐目標 σ_a を
    同時に実現し、直積 {Frobenius^k} × {σ_a} を各有限レベルまで含めて忠実に
    被覆する。M197F（単数側）と M207F（付値側）の合流——柱B B-2（分岐 rec
    の全射性・K^× 貼り合わせ）の joint 全射スライス。 -/
theorem recSurjective_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    Nonempty (RecSurjectiveData p hp hodd) :=
  ⟨recSurjectiveData p hp hodd⟩

end IUT
