/-
# M207F: 分岐 rec の不分岐・Frobenius 側（柱B B-2 不分岐側・並行部品）

M197F（`RecRamifiedSurj`: K^× = p^ℤ × ℤ_p^× の貼り合わせのうち **単数側
O^× = ℤ_p^×** の被覆——各抽象骨格 σ_a を本物の単数 ω(a) で実現し、その
K^× 元 x = (0, ω(a)) の**不分岐成分を自明**にして分岐成分を σ_a に一致
させた）の**ちょうど相補**を閉じる。すなわち M94 `recLevelOne` の
**付値部 ⟨π⟩ = p^ℤ / 不分岐・Frobenius 側**を扱う。

鍵となる観測: K^× 元を x = (k, 1)（付値 k、単数部は自明単数 1）と取ると、
貼り合わせ写像 `recLevelOne` は
  - **不分岐成分** = toZhat(k) = Frobenius^k（M13 の完備化像、k ≠ 0 で
    非自明——M197F の x = (0, ω(a)) では zhat.one に潰れていた側）、
  - **分岐成分** = recInertia(1) = σ_{res1(1)} = σ_1 = id（自明——
    M197F では σ_a という非自明 Galois だった側）
へ送る。従って **M197F（単数側: 不分岐自明・分岐非自明）と M207F（付値側:
不分岐非自明・分岐自明）が K^× = p^ℤ × ℤ_p^× の直積分解に沿って綺麗に
相補**し、貼り合わせ写像が「不分岐 × 分岐」の直積として両因子を独立に
実現することの機械検証となる。付値部については、各有限レベル ℤ/n の
Frobenius 類が付値 k の適当な代表で残らず被覆される（Frobenius 稠密性、
M37 `fullLocalCFT` の付値側被覆のレベル語での再掲）ことも閉じる。

  * M207F-1 `res1_one` — **自明単数の標準代表は 1 と合同**:
    res1(1) ≡ 1 (mod p)（(zpOne).val 1 = mk 1・zres = emod・cast_pow_one）
  * M207F-2 `recInertia_one_trivial` — **分岐側自明**: 自明単数の慣性
    作用 recInertia(1) は恒等（`recInertia_principal` を res1(1) ≡ 1 で）
  * M207F-3 `recUnram_covers` — **付値側被覆（相補の本丸）**: 各付値 k に
    対し、**不分岐成分が toZhat(k)（Frobenius^k）で分岐成分が自明**な
    K^× 元 x = (k, 1) が存在（M197F-4 `recRamSurj_covers` の相補）
  * M207F-4 `recUnram_level_covers` — **Frobenius 稠密性（レベル語）**:
    各有限レベル ℤ/n の任意の Frobenius 類 c は、分岐成分自明のまま
    付値 k の代表で被覆される（`Quot.exists_rep` + `limitProj`）
  * M207F-5 `RecUnramifiedData` / `recUnramifiedData` /
    `recUnramified_exists` — 総括レコード（付値実現子・不分岐 = toZhat(k)・
    分岐自明・不分岐乗法性・各レベル被覆）と witness・存在

意義: M197F が貼り合わせの**単数側**（各 σ_a を実在の ℤ_p^× 単数で被覆・
不分岐成分は自明）を閉じたのに対し、本層はその**付値・不分岐側**
（⟨π⟩ = p^ℤ が toZhat = Frobenius へ写り分岐成分は自明）を閉じる。両層で
K^× = p^ℤ × ℤ_p^× → ẑ × End(O) の貼り合わせが**直積の両因子を独立に
実現する**——付値部は Frobenius 側へ（分岐に触れず）、単数部は慣性側へ
（不分岐に触れず）——ことのレベル 1 完全記述が揃う。

正直な限定: 本層が閉じるのは **付値・不分岐側の被覆**（各 k が
toZhat(k) = Frobenius^k で実現され分岐成分が自明、各有限レベルが被覆
される）のスライスのみ。**ẑ 全体への全射**（toZhat の像 ℤ は ẑ で稠密
だが全射ではない——M13-8 の単射性の裏返し）、分岐 rec の**完全な全射性**
（{σ_a} が抽象 Galois 群 Aut(O) 全体と一致すること）、および
**Λₙ(n ≥ 2) への作用**（塔 O_n 版の rec）は次層に残る（issue #36 の残余）。
全て選択公理不使用（M94/M197F から propext, Quot.sound を継承、
新規 Classical.choice なし）。サブエージェント並行部品。
-/
import IUT.RecGluing

namespace IUT

/-! ## M207F-1: 自明単数の標準代表は 1 と合同 -/

/-- **定理 (M207F-1): 自明単数の標準代表は 1 と合同** — res1(1) ≡ 1
    (mod p)。自明単数 1 = zpOne のレベル 1 値は mk 1（M30-3b の定義から
    直接）で、`res1`/`zres` はその emod（M94-1）だから 1 − 1%p は p の
    倍数。M207F-2 で `recInertia_principal` を適用する橋。 -/
theorem res1_one (p : Nat) (hp : IsPrime p) :
    ((p : Nat) : Int) ∣ res1 p ((zpUnits p hp).one).val - 1 := by
  have h1 : res1 p ((zpUnits p hp).one).val = (1 : Int) % ((p : Nat) : Int) := by
    show zres p ((zpOne p).val 1) = (1 : Int) % ((p : Nat) : Int)
    show (1 : Int) % ((p ^ 1 : Nat) : Int) = (1 : Int) % ((p : Nat) : Int)
    rw [cast_pow_one]
  rw [h1]
  have hediv := Int.emod_add_mul_ediv (1 : Int) ((p : Nat) : Int)
  refine ⟨-((1 : Int) / ((p : Nat) : Int)), ?_⟩
  rw [Int.mul_neg]
  omega

/-! ## M207F-2: 分岐側自明 — 自明単数の慣性作用は恒等 -/

/-- **定理 (M207F-2): 分岐側自明** — 自明単数 1 ∈ ℤ_p^× の貼り合わせ
    分岐成分 `recInertia` は恒等写像。res1(1) ≡ 1（M207F-1）だから主単数核
    `recInertia_principal`（M94-2c）が適用でき σ_1 = id。M197F の x =
    (0, ω(a)) で σ_a（非自明）だった分岐側の、付値側での**相補的自明性**。 -/
theorem recInertia_one_trivial (p : Nat) (hp : IsPrime p) : ∀ t,
    (recInertia p hp (zpUnits p hp).one).map t = t :=
  recInertia_principal p hp (zpUnits p hp).one (res1_one p hp)

/-! ## M207F-3: 付値側被覆（相補の本丸） -/

/-- **定理 (M207F-3): 付値側被覆（相補の本丸）** — 各付値 k ∈ ℤ に対し、
    貼り合わせ相互作用 `recLevelOne` の像が Frobenius^k を掴む K^× の元
    x = (k, 1) ∈ p^ℤ × ℤ_p^× が存在する: **不分岐成分は toZhat(k)**
    （= Frobenius^k、k ≠ 0 で非自明）**かつ分岐成分は自明**（σ_1 = id）。
    M197F-4 `recRamSurj_covers`（不分岐自明・分岐 σ_a）の**ちょうど
    相補**であり、貼り合わせ写像 K^× → ẑ × End(O) の付値・不分岐側の
    被覆（Frobenius の実現）のヘッドライン。 -/
theorem recUnram_covers (p : Nat) (hp : IsPrime p) (k : Int) :
    ∃ x : (QpUnits p hp).carrier,
      (recLevelOne p hp x).1 = toZhat.map k ∧
      ∀ t, (recLevelOne p hp x).2.map t = t := by
  refine ⟨(k, (zpUnits p hp).one), rfl, ?_⟩
  intro t
  exact recInertia_one_trivial p hp t

/-! ## M207F-4: Frobenius 稠密性（レベル語） -/

/-- **定理 (M207F-4): Frobenius 稠密性（レベル語）** — 各有限レベル
    ℤ/n の任意の Frobenius 類 c に対し、**分岐成分を自明に保ったまま**
    不分岐成分の n-射影が c に一致する K^× の元 x = (k, 1)（k は c の
    代表）が存在する。付値部 ⟨π⟩ = p^ℤ が有限レベルの Frobenius を残らず
    被覆する（M37 `fullLocalCFT` の付値側全有限レベル被覆の、貼り合わせ
    `recLevelOne` の語での再掲）。ẑ 全体への全射は成り立たない
    （M13-8 単射性の裏返し・正直な限定）。 -/
theorem recUnram_level_covers (p : Nat) (hp : IsPrime p) (n : Nat)
    (c : (zmod n).carrier) :
    ∃ x : (QpUnits p hp).carrier,
      (limitProj zmodSystem n).map (recLevelOne p hp x).1 = c ∧
      ∀ t, (recLevelOne p hp x).2.map t = t := by
  obtain ⟨k, hk⟩ := Quot.exists_rep c
  refine ⟨(k, (zpUnits p hp).one), ?_, ?_⟩
  · show (limitProj zmodSystem n).map (toZhat.map k) = c
    rw [show (limitProj zmodSystem n).map (toZhat.map k)
        = Quot.mk (modCong n).rel k from rfl, hk]
  · intro t
    exact recInertia_one_trivial p hp t

/-! ## M207F-5: 総括 -/

/-- **M207F-5a: 分岐 rec 付値・不分岐側の被覆データ** — 各付値 k を
    実現する K^× 元（付値部 k・単数部自明）、その不分岐成分が
    toZhat(k) = Frobenius^k に一致すること（付値側被覆）、分岐成分の
    自明性（σ_1 = id）、不分岐成分の乗法性（toZhat 準同型）、および
    各有限レベルの被覆（Frobenius 稠密性）を束ねる純レコード。
    M197F-5 `RecRamifiedSurjData`（単数側）の相補。 -/
structure RecUnramifiedData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) where
  /-- 付値 k を実現する K^× 元 = (k, 自明単数 1)。 -/
  realize : Int → (QpUnits p hp).carrier
  /-- 付値側被覆: 実現子の不分岐成分は Frobenius^k = toZhat(k) に一致。 -/
  realize_unram : ∀ k : Int,
    (recLevelOne p hp (realize k)).1 = toZhat.map k
  /-- 分岐側自明: 実現子の分岐成分は恒等（σ_1 = id）。 -/
  realize_ram_trivial : ∀ (k : Int) t,
    (recLevelOne p hp (realize k)).2.map t = t
  /-- 不分岐成分の乗法性: toZhat(k+l) = Frob^k · Frob^l（準同型）。 -/
  realize_unram_mul : ∀ k l : Int,
    (recLevelOne p hp (realize (intGrp.mul k l))).1
      = zhat.mul (recLevelOne p hp (realize k)).1
          (recLevelOne p hp (realize l)).1
  /-- 各有限レベル被覆: ℤ/n の任意の Frobenius 類は付値 k の代表で被覆。 -/
  realize_level : ∀ (n : Nat) (c : (zmod n).carrier), ∃ k : Int,
    (limitProj zmodSystem n).map (recLevelOne p hp (realize k)).1 = c

set_option linter.unusedVariables false in
/-- **M207F-5b: witness** — 実現子を k ↦ (k, 自明単数 1) とし、M207F-1〜4
    + M94-3b `recLevelOne_mul_unram`（= toZhat 準同型）で純レコードを
    充填（選択公理不使用）。 -/
def recUnramifiedData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    RecUnramifiedData p hp hodd where
  realize := fun k => (k, (zpUnits p hp).one)
  realize_unram := fun _ => rfl
  realize_ram_trivial := fun _ => recInertia_one_trivial p hp
  realize_unram_mul := fun k l => toZhat.map_mul k l
  realize_level := fun n c => by
    obtain ⟨k, hk⟩ := Quot.exists_rep c
    refine ⟨k, ?_⟩
    show (limitProj zmodSystem n).map (toZhat.map k) = c
    rw [show (limitProj zmodSystem n).map (toZhat.map k)
        = Quot.mk (modCong n).rel k from rfl, hk]

/-- **M207F-5c: 存在定理（ヘッドライン）** — 分岐 rec の付値・不分岐側は
    ⟨π⟩ = p^ℤ を toZhat = Frobenius へ写して各 Frobenius 類を被覆し、
    分岐成分は自明に保つ。M197F（単数側）と相補して K^× = p^ℤ × ℤ_p^×
    の貼り合わせが直積の両因子を独立に実現する。柱B B-2（分岐 rec の
    全射性・K^× 貼り合わせ）の付値・不分岐側スライス。 -/
theorem recUnramified_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    Nonempty (RecUnramifiedData p hp hodd) :=
  ⟨recUnramifiedData p hp hodd⟩

end IUT
