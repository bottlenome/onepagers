/-
# M197F: 分岐 rec の全射性・貼り合わせスライス（柱B B-2・並行部品）

M87F（`RecRamified`: 整数 a ごとの Galois 骨格 σ_a := σ_{ω(a)} と
剰余依存性・忠実性）と M94（`RecGluing`: K^× = p^ℤ × ℤ_p^× の
貼り合わせレベル 1 相互作用 recLevelOne / recInertia）の直上に立ち、
issue #36（柱B B-2 残件）の「分岐 rec の全射性——K^× 成分からの
貼り合わせが各生成元を掴むか」のうち **単数側（O^× = μ × U^(1)）の
被覆スライス** を閉じる。

鍵となる観測: **Teichmüller 代表 ω(a)（p ∤ a）はそれ自身が本物の
ℤ_p^× の単数**（M36-2b `isZpUnit_teich`）であり、そのレベル 1 標準
代表は a と合同（M118F-1 `teich_val_one` + M94-1 `res1`/`zres`）。
従って貼り合わせ相互作用の分岐成分 `recInertia` をこの本物の単数へ
適用すると、剰余依存性（M87F-1 `eisGal_residue`）により **抽象骨格
σ_a とちょうど一致** する。これは「整数パラメタ a で添字された
Galois 骨格 {σ_a}（M87F）が、K^× = p^ℤ × ℤ_p^× の**実在の単数群
ℤ_p^× の元**の相互作用像で残らず実現される」という **分岐 rec の
単数側全射性（被覆）** の機械検証である。

  * M197F-1 `res1_teich_congr` — **ω(a) の標準代表は a と合同**:
    res1(ω(a)) ≡ a (mod p)（`teich_val_one` + `zres` = emod + `cast_pow_one`）
  * M197F-2 `recInertia_teich_eq` — **被覆（本丸）**: 本物の単数
    ⟨ω(a), 単数性⟩ の分岐成分 recInertia は抽象骨格 σ_a に一致
    （`eisGal_residue` を res1(ω(a)) ≡ a で適用）
  * M197F-3 `recInertia_teich_lambda` — λ 上の明示: recInertia(ω(a))(λ)
    = ω(a)·λ（M197F-2 を λ で評価 + M86F-5b `eisAut_lambda`）
  * M197F-4 `recRamSurj_covers` — **K^× からの被覆**: 各 a（p ∤ a）に
    対し、不分岐成分が自明で分岐成分が σ_a に一致する K^× の元
    x = (0, ω(a)) が存在（貼り合わせ recLevelOne での実現）
  * M197F-5 `RecRamifiedSurjData` / `recRamifiedSurjData` /
    `recRamifiedSurj_exists` — 総括レコード（実現子・被覆等式・λ 明示・
    不分岐自明性・忠実性 = 被覆は単射）と witness・存在

意義: M87F は分岐 rec のレベル 1 骨格を「整数 a で添字した σ_a の族」
として立て、M94 は K^× = p^ℤ × ℤ_p^× の貼り合わせ写像を構成したが、
「その像が σ_a を**残らず**掴む（全射・被覆）」ことは未接続だった。
本層は Teichmüller 代表が実在の単数であるという一点で両者を橋渡しし、
**単数側の分岐 rec は像として σ_a 族全体を被覆し、かつ忠実（剰余が
異なれば作用も異なる）＝(ℤ/p)^× 上の全単射**であることを閉じる。

正直な限定: 本層が閉じるのは **単数側 O^× の被覆（各 σ_a が実在の
ℤ_p^× 単数で実現される）とその単射性** のスライスのみ。分岐 rec の
**完全な全射性**（{σ_a} が抽象 Galois 群 Aut(O) の全体と一致すること）、
**K^× 全体の貼り合わせ**（付値部 ⟨π⟩ = p^ℤ の不分岐/Frobenius 側の
全射は M37 `fullLocalCFT` 側に分離）、および **Λₙ(n ≥ 2) への作用**
（塔 O_n 版の rec）は次層に残る（issue #36 の残余）。
全て選択公理不使用（M94/M87F から propext, Quot.sound を継承、
新規 Classical.choice なし）。サブエージェント並行部品。
-/
import IUT.RecGluing
import IUT.ZpUnitDecomp

namespace IUT

/-! ## M197F-1: ω(a) の標準代表は a と合同 -/

/-- **定理 (M197F-1): ω(a) の標準代表は a と合同** — res1(ω(a)) ≡ a
    (mod p)。Teichmüller 代表のレベル 1 値は a（M118F-1 `teich_val_one`）
    であり、`res1`/`zres` はその emod（M94-1）だから、a − a%p は p の
    倍数。M197F-2 で剰余依存性を適用する橋。 -/
theorem res1_teich_congr (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    ((p : Nat) : Int) ∣ res1 p (teich p hp a) - a := by
  have h1 : res1 p (teich p hp a) = a % ((p : Nat) : Int) := by
    show zres p ((teich p hp a).val 1) = a % ((p : Nat) : Int)
    rw [teich_val_one]
    show a % ((p ^ 1 : Nat) : Int) = a % ((p : Nat) : Int)
    rw [cast_pow_one]
  rw [h1]
  have hediv := Int.emod_add_mul_ediv a ((p : Nat) : Int)
  refine ⟨-(a / ((p : Nat) : Int)), ?_⟩
  rw [Int.mul_neg]
  omega

/-! ## M197F-2: 被覆（本丸）— 本物の単数の分岐成分は σ_a に一致 -/

/-- **定理 (M197F-2): 被覆（本丸）** — 本物の ℤ_p^× 単数
    ⟨ω(a), 単数性⟩ に貼り合わせ分岐成分 `recInertia` を適用すると、
    整数 a で添字された抽象 Galois 骨格 σ_a（M87F `eisGal`）に
    **完全に一致**する。証明は recInertia = σ_{res1(ω(a))} の展開と、
    res1(ω(a)) ≡ a（M197F-1）による剰余依存性 M87F-1 `eisGal_residue`。
    「σ_a 族は実在の単数群 ℤ_p^× の相互作用像で残らず実現される」
    = 分岐 rec の単数側全射性（被覆）の実体。 -/
theorem recInertia_teich_eq (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) : ∀ t,
    (recInertia p hp ⟨teich p hp a, isZpUnit_teich p hp ha⟩).map t
      = (eisGal p hp a ha).map t := by
  intro t
  exact eisGal_residue p hp
    (res1_unit_not_dvd p (teich p hp a) (isZpUnit_teich p hp ha)) ha
    (res1_teich_congr p hp ha) t

/-! ## M197F-3: λ 上の明示 -/

/-- **定理 (M197F-3): 被覆の λ 明示** — recInertia(⟨ω(a),·⟩)(λ) = ω(a)·λ。
    M197F-2 を λ で評価し、σ_a(λ) = ω(a)·λ（M86F-5b `eisAut_lambda`）
    を合わせる。本物の単数の分岐作用が λ を Teichmüller 倍する。 -/
theorem recInertia_teich_lambda (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    (recInertia p hp ⟨teich p hp a, isZpUnit_teich p hp ha⟩).map (eisLambda p)
      = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p) := by
  rw [recInertia_teich_eq p hp ha (eisLambda p)]
  exact eisAut_lambda p (teich p hp a) (teich_pow_rpow_one p hp ha) hp.1

/-! ## M197F-4: K^× からの被覆 -/

/-- **定理 (M197F-4): K^× からの被覆** — 各剰余 a（p ∤ a）に対し、
    貼り合わせ相互作用 `recLevelOne` の像が σ_a を掴む K^× の元
    x = (0, ω(a)) ∈ p^ℤ × ℤ_p^× が存在する: **不分岐成分は自明**
    （付値部 0 → toZhat 0 = 1）**かつ分岐成分は σ_a に一致**。
    貼り合わせ写像 K^× → ẑ × End(O) の単数側全射性（各生成元の被覆）
    のヘッドライン。 -/
theorem recRamSurj_covers (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    ∃ x : (QpUnits p hp).carrier,
      (recLevelOne p hp x).1 = zhat.one ∧
      ∀ t, (recLevelOne p hp x).2.map t = (eisGal p hp a ha).map t := by
  refine ⟨((0 : Int), ⟨teich p hp a, isZpUnit_teich p hp ha⟩),
    toZhat.map_one, ?_⟩
  intro t
  exact recInertia_teich_eq p hp ha t

/-! ## M197F-5: 総括 -/

/-- **M197F-5a: 分岐 rec 単数側全射（被覆）データ** — 各剰余 a を
    実現する本物の単数、その分岐成分が σ_a に一致すること（被覆）、
    λ 上の明示（ω(a)·λ）、K^× 元としての不分岐成分自明性、および
    忠実性（剰余が異なれば λ 上の作用も異なる＝被覆は (ℤ/p)^× 上単射）
    を束ねる純レコード。 -/
structure RecRamifiedSurjData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) where
  /-- 剰余 a を実現する本物の ℤ_p^× 単数（= Teichmüller 代表 ω(a)）。 -/
  realize : (a : Int) → ¬ ((p : Nat) : Int) ∣ a → (zpUnits p hp).carrier
  /-- 被覆: 実現子の分岐成分は抽象骨格 σ_a に完全一致。 -/
  realize_eq : ∀ (a : Int) (ha : ¬ ((p : Nat) : Int) ∣ a) t,
    (recInertia p hp (realize a ha)).map t = (eisGal p hp a ha).map t
  /-- λ 上の明示: 実現子(λ) = ω(a)·λ。 -/
  realize_lambda : ∀ (a : Int) (ha : ¬ ((p : Nat) : Int) ∣ a),
    (recInertia p hp (realize a ha)).map (eisLambda p)
      = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p)
  /-- K^× 元 (0, 実現子) の不分岐成分は自明（付値部 0 → Frobenius 1）。 -/
  realize_unram_trivial : ∀ (a : Int) (ha : ¬ ((p : Nat) : Int) ∣ a),
    (recLevelOne p hp ((0 : Int), realize a ha)).1 = zhat.one
  /-- 忠実性: p ∤ (a − b) なら σ_a(λ) ≠ σ_b(λ)（被覆は剰余で単射）。 -/
  faithful : ∀ {a b : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hb : ¬ ((p : Nat) : Int) ∣ b), ¬ ((p : Nat) : Int) ∣ (a - b) →
    (eisGal p hp a ha).map (eisLambda p)
      ≠ (eisGal p hp b hb).map (eisLambda p)

/-- **M197F-5b: witness** — Teichmüller 代表を実現子とし、M197F-1〜4 +
    M87F-4 `eisGal_faithful` で純レコードを充填（選択公理不使用）。 -/
def recRamifiedSurjData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    RecRamifiedSurjData p hp hodd where
  realize := fun a ha => ⟨teich p hp a, isZpUnit_teich p hp ha⟩
  realize_eq := fun a ha => recInertia_teich_eq p hp ha
  realize_lambda := fun a ha => recInertia_teich_lambda p hp ha
  realize_unram_trivial := fun _ _ => toZhat.map_one
  faithful := fun ha hb hab => eisGal_faithful p hp hodd ha hb hab

/-- **M197F-5c: 存在定理（ヘッドライン）** — 分岐 rec の単数側は
    実在の ℤ_p^× 単数の相互作用像で σ_a 族全体を忠実に被覆する。
    柱B B-2（分岐 rec の全射性・K^× 貼り合わせ）の単数側スライス。 -/
theorem recRamifiedSurj_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    Nonempty (RecRamifiedSurjData p hp hodd) :=
  ⟨recRamifiedSurjData p hp hodd⟩

end IUT
