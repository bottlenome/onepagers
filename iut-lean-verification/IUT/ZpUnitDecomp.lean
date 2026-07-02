/-
  IUT/ZpUnitDecomp.lean — M118F: ℤ_p^× の完全分解 — μ_{p−1} × (1+pℤ_p) と
  全単数の可逆性

  ℤ_p^× = μ_{p−1} × U^(1) の分解定理群を一箇所に束ね、単数群側の
  構造論を完結させる。分解の存在（M35 `unit_decomposition`）に
  一意性・Teichmüller 部分の可逆性・全単数の可逆性・乗法閉性を加え、
  ℤ_p^× が μ_{p−1} × (1+pℤ_p) の内部直積であることの witness 束
  `ZpUnitGroupData` を構成する。

  * M118F-1 `teich_val_one` — ω(a) のレベル 1 値は a（M33-7
    `teich_reduction` の再輸出。分解のレベル 1 読み出しの基点）
  * M118F-2 `teich_inv_exists` — **Teichmüller 部分の可逆性**:
    p ∤ a なら ω(a)·ω(b) = 1 なる b（= a^{p−2}、Fermat の小定理
    a·a^{p−2} = a^{p−1} ≡ 1 (mod p) と ω の剰余依存性 M35-3 による。
    Bezout 不要の明示構成）
  * M118F-3 `unit_decomposition_unique` — **分解の一意性**:
    ω(a)·v = ω(a')·v'（v, v' 主単数）なら ω(a) = ω(a') かつ v = v'
    （M35-5 `decomposition_unique` の再輸出形）
  * M118F-4 `zp_unit_inv_exists` — **全単数の可逆性**: IsZpUnit x なら
    x·y = 1 なる y が存在（M36-4 `zpUnitInv` = x^{p−2}·(x^{p−1})^{−1}
    の明示構成をそのまま使用、選択公理不使用）
  * M118F-5 `zp_unit_mul` / `zp_unit_one` — 単数の乗法閉性
    （M36-2 の再輸出）と 1 の単数性
  * M118F-6 `ZpUnitGroupData` / `zpUnitGroupData` / `zpUnitGroup_exists` —
    **総括**: 分解の存在・一意性・両因子と全体の可逆性・乗法閉性を
    束ねた witness 構造とその実現

  意義: 柱B B-2（issue #36）の単数群側完結。分解の存在（M107 系）に
  一意性・可逆性を加え、ℤ_p^× が μ_{p−1} × U^(1) の内部直積である
  ことの witness 束。M107 の [u]λ = ω(u mod p)λ・M94 recLevelOne と
  合わせ K^× = p^ℤ × μ_{p−1} × U^(1) の作用の完全記述に接近する。

  正直な申告: 本モジュールは witness 束（Prop 構造体）であり、
  ℤ_p^× の Grp 化そのものは M36 `zpUnits` が担う。K^× 全体の
  p^ℤ × μ_{p−1} × U^(1) 直積分解の明示同型は次層。主単数の逆元は
  M30 `zpGeomInv`（M36 経由）を用いたため M114F `principalUnitInv`
  は本ファイルでは未使用（import は依存整合のため保持）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.UnitDecomposition
import IUT.PrincipalUnitGroup
import IUT.PadicGeometric
import IUT.ZpUnits

namespace IUT

/-! ## Teichmüller 代表のレベル 1 値 -/

/-- **M118F-1: ω(a) のレベル 1 値は a** — Teichmüller 代表は剰余体の
    持ち上げ（M33-7 `teich_reduction` の再輸出。分解のレベル 1 読み出し
    の基点として本ファイルの名前空間に固定する）。 -/
theorem teich_val_one (p : Nat) (hp : IsPrime p) (a : Int) :
    (teich p hp a).val 1 = Quot.mk (modCong (p ^ 1)).rel a :=
  teich_reduction p hp a

/-! ## Teichmüller 部分の可逆性 -/

/-- **定理 (M118F-2): Teichmüller 部分の可逆性** — p ∤ a なら
    ω(a)·ω(b) = 1 なる p と素な b が存在する。b = a^{p−2} の明示構成:
    a·a^{p−2} = a^{p−1} ≡ 1 (mod p)（Fermat の小定理）と ω の剰余
    依存性（M35-3）から ω(a·a^{p−2}) = ω(1) = 1。Bezout 不要。 -/
theorem teich_inv_exists (p : Nat) (hp : IsPrime p) (a : Int)
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    ∃ b : Int, (¬ ((p : Nat) : Int) ∣ b) ∧
      zpMul p (teich p hp a) (teich p hp b) = zpOne p := by
  refine ⟨ipow a (p - 2), not_dvd_ipow p hp ha (p - 2), ?_⟩
  rw [← teich_mul p hp a (ipow a (p - 2))]
  have he : a * ipow a (p - 2) = ipow a (p - 1) := by
    have hpp : p - 1 = p - 2 + 1 := by
      have := hp.1
      omega
    rw [hpp]
    show a * ipow a (p - 2) = ipow a (p - 2) * a
    rw [Int.mul_comm]
  rw [he, teich_congr p hp (flt_unit p hp ha), teich_one]

/-! ## 分解の一意性 -/

set_option linter.unusedVariables false in
/-- **定理 (M118F-3): 分解の一意性** — ω(a)·v = ω(a')·v'（v, v' 主単数、
    p ∤ a, a'）なら ω(a) = ω(a') かつ v = v'。レベル 1 の合同の望遠鏡和
    と ω(a)^{p−2} による消去（M35-5 `decomposition_unique` の再輸出形。
    ha' は対称性のための API 保持で、証明には ha のみで足りる）。 -/
theorem unit_decomposition_unique (p : Nat) (hp : IsPrime p) {a a' : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) (ha' : ¬ ((p : Nat) : Int) ∣ a')
    {v v' : (Zp p).carrier}
    (hv : IsPrincipalUnit p v) (hv' : IsPrincipalUnit p v')
    (h : zpMul p (teich p hp a) v = zpMul p (teich p hp a') v') :
    teich p hp a = teich p hp a' ∧ v = v' :=
  decomposition_unique p hp ha hv hv' h

/-! ## 全単数の可逆性 -/

/-- **定理 (M118F-4): 全単数の可逆性** — IsZpUnit x なら x·y = 1 なる
    y が存在する。y = x^{p−2}·(x^{p−1})^{−1}（M36-4 `zpUnitInv`:
    x^{p−1} は古典形 Fermat で主単数となり幾何級数逆元 M30 が適用
    できる）の明示構成で、代表元の抽出（選択公理）を用いない。 -/
theorem zp_unit_inv_exists (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier)
    (hx : IsZpUnit p x) : ∃ y, zpMul p x y = zpOne p := by
  refine ⟨zpUnitInv p hp x hx, ?_⟩
  rw [zpMul_comm]
  exact zpUnitInv_mul p hp x hx

/-! ## 単数の乗法閉性 -/

/-- **M118F-5a: 単数は積で閉じる**（Euclid の補題。M36-2a の再輸出）。 -/
theorem zp_unit_mul (p : Nat) (hp : IsPrime p) {x y : (Zp p).carrier}
    (hx : IsZpUnit p x) (hy : IsZpUnit p y) : IsZpUnit p (zpMul p x y) :=
  isZpUnit_mul p hp hx hy

/-- **M118F-5b: 1 は単数**（レベル 1 の代表 1 は p と素）。 -/
theorem zp_unit_one (p : Nat) (hp : IsPrime p) : IsZpUnit p (zpOne p) :=
  ⟨1, rfl, not_dvd_one p hp.1⟩

/-! ## 総括: ℤ_p^× = μ_{p−1} × (1+pℤ_p) の witness 束 -/

/-- **M118F-6a: ℤ_p^× の完全分解データ** — 分解の存在・一意性・
    Teichmüller 因子の可逆性・全単数の可逆性・乗法閉性・1 の単数性を
    束ねた Prop 構造体。ℤ_p^× が μ_{p−1} × U^(1) の内部直積であること
    の witness 束。 -/
structure ZpUnitGroupData (p : Nat) (hp : IsPrime p) : Prop where
  /-- 分解の存在: x ≡ a (mod p)、p ∤ a なら x = ω(a)·u（u 主単数）。 -/
  decomp : ∀ (x : (Zp p).carrier) (a : Int), ¬ ((p : Nat) : Int) ∣ a →
    x.val 1 = Quot.mk (modCong (p ^ 1)).rel a →
    ∃ u, IsPrincipalUnit p u ∧ x = zpMul p (teich p hp a) u
  /-- 分解の一意性: ω(a)·v = ω(a')·v' なら因子ごとに一致。 -/
  unique : ∀ (a a' : Int) (v v' : (Zp p).carrier),
    ¬ ((p : Nat) : Int) ∣ a → ¬ ((p : Nat) : Int) ∣ a' →
    IsPrincipalUnit p v → IsPrincipalUnit p v' →
    zpMul p (teich p hp a) v = zpMul p (teich p hp a') v' →
    teich p hp a = teich p hp a' ∧ v = v'
  /-- Teichmüller 因子の可逆性: p ∤ a なら ω(a)·ω(b) = 1 なる b。 -/
  teich_inv : ∀ a : Int, ¬ ((p : Nat) : Int) ∣ a →
    ∃ b : Int, (¬ ((p : Nat) : Int) ∣ b) ∧
      zpMul p (teich p hp a) (teich p hp b) = zpOne p
  /-- 全単数の可逆性: IsZpUnit x なら x·y = 1 なる y。 -/
  inv : ∀ x : (Zp p).carrier, IsZpUnit p x → ∃ y, zpMul p x y = zpOne p
  /-- 単数の乗法閉性。 -/
  mul_closed : ∀ x y : (Zp p).carrier, IsZpUnit p x → IsZpUnit p y →
    IsZpUnit p (zpMul p x y)
  /-- 1 は単数。 -/
  one_unit : IsZpUnit p (zpOne p)

/-- **定理 (M118F-6b): 完全分解データの実現** — 全フィールドを
    M33–M36 の既証明と本ファイルの M118F-2/3/4 で埋める。 -/
theorem zpUnitGroupData (p : Nat) (hp : IsPrime p) : ZpUnitGroupData p hp :=
  { decomp := fun x _ ha hx => unit_decomposition p hp x ha hx
    unique := fun _ _ _ _ ha ha' hv hv' h =>
      unit_decomposition_unique p hp ha ha' hv hv' h
    teich_inv := fun a ha => teich_inv_exists p hp a ha
    inv := fun x hx => zp_unit_inv_exists p hp x hx
    mul_closed := fun _ _ hx hy => zp_unit_mul p hp hx hy
    one_unit := zp_unit_one p hp }

/-- **M118F-6c**: 完全分解データの非空性（Nonempty 形の再輸出）。 -/
theorem zpUnitGroup_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (ZpUnitGroupData p hp) :=
  ⟨zpUnitGroupData p hp⟩

end IUT
