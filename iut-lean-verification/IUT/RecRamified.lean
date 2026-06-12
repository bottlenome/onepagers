/-
  IUT/RecRamified.lean — M87F（柱B 第3段前半: 分岐相互写像のレベル 1 骨格）

  M86F は σ_a := σ_{ω(a)}（p ∤ a）として Gal(ℚ_p(λ)/ℚ_p) の骨格
  （p−1 個の相異なる環自己準同型）を構成した。本ファイルはこれを
  **分岐相互写像 rec のレベル 1 成分**として読み直す: Lubin–Tate
  相互法則 rec(u)·t = [u^{−1}](t) は n = 1 の捻れ層 Λ₁ 上では
  剰余 u mod p のみを通って作用するから、単数 u ∈ ℤ_p^× の作用は
  σ_{ū} : λ ↦ ω(ū)λ で実現される。本ファイルはこの
  **(ℤ/p)^× → Gal(ℚ_p(λ)/ℚ_p)** という準同型の簿記
  — 剰余依存性（well-definedness）・乗法性・主単数核・忠実性 —
  を完成し、M37 の不分岐 rec（ℚ_p^× = p^ℤ × ℤ_p^× の付値部）と
  対をなす分岐部のレベル 1 witness を立てる。

  * M87F-1 `eisGal_residue` — **剰余依存性（well-definedness）**:
    a ≡ b (mod p) なら σ_a = σ_b（M35-3b teich_congr: ω(a) = ω(b) +
    M86F-6d eisAut_congr）— **作用は剰余類のみで決まり (ℤ/p)^× に降りる**
  * M87F-2 `recRam_mul` — **乗法性**: σ_a ∘ σ_b = σ_{ab}
    （M86F-7c eisGal_mul の rec 言語での再掲）
  * M87F-3 `eisGal_principal_trivial` — **主単数核**: a ≡ 1 (mod p)
    なら σ_a = id（ω(a) = ω(1) = 1 は M35-3b + M33-8b teich_one、
    そして M86F-6c eisAut_one）— **U^{(1)} ⊆ ker(分岐 rec の Λ₁ 成分)**、
    rec のフィルトレーション両立性のレベル 1 の影
  * M87F-4 `eisGal_faithful` — **剰余上の忠実性**: p ∤ (a − b) なら
    σ_a(λ) ≠ σ_b(λ)（M86F-8 eisGal_distinct）— 核はちょうど主単数
  * M87F-5 `RecRamifiedLevelOneData` / `recRamLevelOne` /
    `recRam_exists` — **柱B 第3段前半の総括インターフェース**:
    作用・剰余依存性・乗法性・主単数核・忠実性・λ 上の明示式
    （σ_a(λ) = ω(a)λ）・[π]-作用との可換性（M86F-9 eisAut_eisF）を
    束ねた純レコードと、その witness・存在定理
  * M87F-6 `recRam_fixes_base` — ストレッチ: **分岐作用は ℤ_p の像を
    まるごと固定**（M86F-5a eisAut_const の構造上での再掲）—
    不分岐側（M37 の付値部）と分岐側の作用の独立性の骨格

  Λₙ（n ≥ 2）への作用・rec の完全な分岐成分（K^× 全体からの写像と
  しての貼り合わせ）・全射性（Gal の分類）は未形式化。本構造は M37 の
  不分岐 rec と対をなすレベル 1 の witness。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.EisensteinGalois

namespace IUT

/-! ## 剰余依存性: 作用は (ℤ/p)^× に降りる -/

/-- **定理 (M87F-1): 剰余依存性（well-definedness）** —
    a ≡ b (mod p) なら σ_a = σ_b: ω(a) = ω(b)（M35-3b teich_congr）
    だから σ_{ω(a)} = σ_{ω(b)}（M86F-6d eisAut_congr）。
    **単数の Λ₁ への作用は剰余類 u mod p のみで決まる** —
    写像 a ↦ σ_a は (ℤ/p)^× → Gal(ℚ_p(λ)/ℚ_p) に降りる。 -/
theorem eisGal_residue (p : Nat) (hp : IsPrime p) {a b : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) (hb : ¬ ((p : Nat) : Int) ∣ b)
    (hab : ((p : Nat) : Int) ∣ a - b) : ∀ t,
    (eisGal p hp a ha).map t = (eisGal p hp b hb).map t :=
  eisAut_congr p (teich_congr p hp hab)
    (teich_pow_rpow_one p hp ha) (teich_pow_rpow_one p hp hb) hp.1

/-! ## 乗法性: rec は準同型 -/

/-- **M87F-2: 乗法性（rec 言語での再掲）** — σ_a ∘ σ_b = σ_{ab}
    （M86F-7c eisGal_mul）。分岐 rec のレベル 1 成分は
    (ℤ/p)^× の乗法を Galois 合成に運ぶ準同型。 -/
theorem recRam_mul (p : Nat) (hp : IsPrime p) {a b : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) (hb : ¬ ((p : Nat) : Int) ∣ b)
    (hab : ¬ ((p : Nat) : Int) ∣ (a * b)) : ∀ t,
    (eisGal p hp a ha).map ((eisGal p hp b hb).map t)
      = (eisGal p hp (a * b) hab).map t :=
  eisGal_mul p hp ha hb hab

/-! ## 主単数核: U^{(1)} は Λ₁ に自明に作用 -/

/-- **定理 (M87F-3): 主単数核** — a ≡ 1 (mod p) なら σ_a = id:
    ω(a) = ω(1)（M35-3b）= 1（M33-8b teich_one）だから
    σ_a = σ_1 = id（M86F-6d + M86F-6c eisAut_one）。
    **U^{(1)} ⊆ ker(分岐 rec の Λ₁ 成分)** — Lubin–Tate rec が
    単数フィルトレーションを分岐フィルトレーションに運ぶことの
    レベル 1 の影。 -/
theorem eisGal_principal_trivial (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) (h1 : ((p : Nat) : Int) ∣ a - 1) :
    ∀ t, (eisGal p hp a ha).map t = t := by
  intro t
  have hω : teich p hp a = (zpRing p).one :=
    (teich_congr p hp h1).trans (teich_one p hp)
  have h1pow : rpow (zpRing p) (zpRing p).one (p - 1) = (zpRing p).one :=
    rpow_one_base (zpRing p) (p - 1)
  exact (eisAut_congr p hω (teich_pow_rpow_one p hp ha) h1pow hp.1 t).trans
    (eisAut_one p h1pow hp.1 t)

/-! ## 忠実性: 核はちょうど主単数 -/

/-- **定理 (M87F-4): 剰余上の忠実性** — p ∤ (a − b) なら
    σ_a(λ) ≠ σ_b(λ)（M86F-8 eisGal_distinct）。M87F-1 と合わせて
    **σ_a = σ_b ⟺ a ≡ b (mod p)**: 誘導される
    (ℤ/p)^× → Gal(ℚ_p(λ)/ℚ_p) は単射、核はちょうど主単数（M87F-3）。 -/
theorem eisGal_faithful (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    {a b : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hb : ¬ ((p : Nat) : Int) ∣ b)
    (hab : ¬ ((p : Nat) : Int) ∣ (a - b)) :
    (eisGal p hp a ha).map (eisLambda p)
      ≠ (eisGal p hp b hb).map (eisLambda p) :=
  eisGal_distinct p hp hodd ha hb hab

/-! ## 柱B 第3段前半の総括インターフェース -/

/-- **M87F-5a: 分岐相互写像レベル 1 データ** — 単数の剰余を通した
    Λ₁ への Galois 作用 a ↦ σ_a を、rec の分岐成分の骨格として
    要求される全簿記とともに束ねる:
    剰余依存性（well-definedness）・乗法性（準同型性）・主単数核
    （フィルトレーション両立）・忠実性（単射性）・λ 上の明示式
    （σ_a(λ) = ω(a)λ = Lubin–Tate [ω(a)]-作用のレベル 1 形）・
    [π]-作用との可換性（Galois × Lubin–Tate の両立）。 -/
structure RecRamifiedLevelOneData (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) where
  /-- 作用: p ∤ a なる a ごとの O の環自己準同型 σ_a。 -/
  act : (a : Int) → ¬ ((p : Nat) : Int) ∣ a →
    RingHom (eisRing p) (eisRing p)
  /-- 剰余依存性: a ≡ b (mod p) なら σ_a = σ_b（(ℤ/p)^× に降りる）。 -/
  act_residue : ∀ {a b : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hb : ¬ ((p : Nat) : Int) ∣ b), ((p : Nat) : Int) ∣ a - b →
    ∀ t, (act a ha).map t = (act b hb).map t
  /-- 乗法性: σ_a ∘ σ_b = σ_{ab}。 -/
  act_mul : ∀ {a b : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hb : ¬ ((p : Nat) : Int) ∣ b)
    (hab : ¬ ((p : Nat) : Int) ∣ (a * b)), ∀ t,
    (act a ha).map ((act b hb).map t) = (act (a * b) hab).map t
  /-- 主単数核: a ≡ 1 (mod p) なら σ_a = id。 -/
  act_principal : ∀ {a : Int} (ha : ¬ ((p : Nat) : Int) ∣ a),
    ((p : Nat) : Int) ∣ a - 1 → ∀ t, (act a ha).map t = t
  /-- 忠実性: p ∤ (a − b) なら σ_a(λ) ≠ σ_b(λ)。 -/
  act_faithful : ∀ {a b : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hb : ¬ ((p : Nat) : Int) ∣ b), ¬ ((p : Nat) : Int) ∣ (a - b) →
    (act a ha).map (eisLambda p) ≠ (act b hb).map (eisLambda p)
  /-- λ 上の明示式: σ_a(λ) = ω(a)·λ。 -/
  act_lambda : ∀ (a : Int) (ha : ¬ ((p : Nat) : Int) ∣ a),
    (act a ha).map (eisLambda p)
      = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p)
  /-- [π]-作用との可換性: σ_a(f(t)) = f(σ_a(t))（f = Lubin–Tate）。 -/
  act_frobenius_compat : ∀ (a : Int) (ha : ¬ ((p : Nat) : Int) ∣ a)
    (t : (eisRing p).carrier),
    (act a ha).map (eisF p t) = eisF p ((act a ha).map t)

/-- **定理 (M87F-5b): witness** — M86F の Galois 骨格 σ_a := σ_{ω(a)}
    が分岐 rec のレベル 1 データを成す（M87F-1〜4 + M86F-5b/9 から
    純レコードで充填、選択公理不使用）。 -/
def recRamLevelOne (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    RecRamifiedLevelOneData p hp hodd where
  act := fun a ha => eisGal p hp a ha
  act_residue := fun ha hb hab => eisGal_residue p hp ha hb hab
  act_mul := fun ha hb hab => recRam_mul p hp ha hb hab
  act_principal := fun ha h1 => eisGal_principal_trivial p hp ha h1
  act_faithful := fun ha hb hab => eisGal_faithful p hp hodd ha hb hab
  act_lambda := fun a ha =>
    eisAut_lambda p (teich p hp a) (teich_pow_rpow_one p hp ha) hp.1
  act_frobenius_compat := fun a ha t =>
    eisAut_eisF p (teich p hp a) (teich_pow_rpow_one p hp ha) hp.1 t

/-- **M87F-5c: 存在定理（ヘッドライン）** — 分岐相互写像のレベル 1
    骨格は存在する。M37 の不分岐 rec（fullLocalCFT）と対をなす
    柱B 第3段前半の総括。 -/
theorem recRam_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    Nonempty (RecRamifiedLevelOneData p hp hodd) :=
  ⟨recRamLevelOne p hp hodd⟩

/-! ## ストレッチ: 不分岐側との独立性 -/

/-- **定理 (M87F-6): 分岐作用は基礎環 ℤ_p を固定** —
    σ_a(eisOf c) = eisOf c（M86F-5a eisAut_const の構造上での再掲）。
    分岐 rec の Λ₁ 成分は ℤ_p の像（不分岐側の係数環）には一切
    触れない — ℚ_p^× = p^ℤ × ℤ_p^×（M37）の分解に対応して
    **不分岐作用（Frobenius、付値部）と分岐作用（単数部）が
    独立に働く**ことのレベル 1 の骨格。 -/
theorem recRam_fixes_base (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    {a : Int} (ha : ¬ ((p : Nat) : Int) ∣ a) (c : (Zp p).carrier) :
    ((recRamLevelOne p hp hodd).act a ha).map ((eisOf p).map c)
      = (eisOf p).map c :=
  eisAut_const p (teich p hp a) (teich_pow_rpow_one p hp ha) hp.1 c

end IUT
