/-
  IUT/CyclotomicCharIso.lean — CCI（A3 M4a: レベル指標同型
  Gal(ℚ(ζ_{3^ℓ})/ℚ) ≅ (ℤ/3^ℓ)^×）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・実円分体
     ℚ(ζ_{3^ℓ}) = ℚ[x]/(Φ_{3^ℓ}) の上での、レベル ℓ の指標同型
     Gal(ℚ(ζ_{3^ℓ})/ℚ) ≅ (ℤ/3^ℓ)^× を本物に確立する）。指標方向 χ_ℓ は
     σ ↦ ctr_charG σ（σ(ζ)=ζ^a の a）を群準同型 `cciToUnits` へ昇格し、
     ★新規数学の**指標積公式 `cci_charG_mul`**（char(σ·τ)=char σ·char τ mod 3^ℓ・
     ロードマップ §4.3 が名指しした欠落）で乗法性を閉じる。逆方向 σ_a は
     代入自己同型 `csaAut`（逆元 witness は `zpuInvL`・choice-free）で `cciFromUnits` に
     昇格し、単射（`cae_aut_ext`）＋全射（`csaAut`）＋左右の逆元法則
     `cci_left_inv`/`cci_right_inv` で同型レコード `CciIsoData` を完全証明する。
     円分切片の可換性 `cci_gal_comm`（Gal(ℚ(ζ_{3^ℓ})/ℚ) はアーベル）も無償の副産物。

  **complete_pct 影響**: A3 M4a——各段 Gal(ℚ(ζ_{3^ℓ})/ℚ) ≅ (ℤ/3^ℓ)^× を本物に
  確立（指標同型・単射 cae ＋ 全射 csa ＋ 積公式 cci_charG_mul）。円分切片の
  可換性も副産物。**本ファイル単体では complete_pct 未設定**（逆極限 ℤ₃^× の
  極限同型 M4b＝cli 到達で反映）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・円分体 ℚ(ζ_{3^ℓ}) の忠実な部分ケース（一般素数 p は含めない）。
   (ii)  本ファイルは**各レベル ℓ の指標同型（レベル同型）まで**。逆極限
         ℤ₃^× ≅ lim (ℤ/3^ℓ)^× への昇格・射影全射性は M4b（cli）・M4c（cps）の射程。
   (iii) 逆方向の代入自己同型 σ_a は明示逆元 witness（`zpuInvL`）を受け取る設計
         （core FieldAut は明示 invFun を要する）。witness の choice-free 供給は
         zpu（Hensel 持ち上げ）が担い、本ファイルはそれを (ℤ/3^ℓ)^× の元から取り出す。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]・Classical.choice 無し）。
  禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/
  build.sh/dashboard/graph/tools は不更新・親が統合）。3^ℓ は omega 不可のため
  冪補題は依存（zpu/ctm）に集約済み。
-/
import IUT.Zmod3PowUnits
import IUT.CyclotomicResTower
import IUT.CyclotomicSubAut
import IUT.CyclotomicAutExt
import IUT.CyclotomicMuTower

namespace IUT

/-! ## CCI-1: 一般化指標一意性（ctr_index_one の ℓ・一般ターゲット版） -/

/-- **CCI-1: ζ_ℓ^k = ζ_ℓ^a・a < 3^ℓ ⟹ k % 3^ℓ = a**（`ctr_index_one` の忠実な
    一般化）。左辺を k%3^ℓ に落とし（`ctm_pow_mod`）、両者 < 3^ℓ の相異性
    （`ctm_powers_distinct`）で場合分けを閉じる。 -/
theorem cci_indexG (ℓ : Nat) (hℓ : 1 ≤ ℓ) (k a : Nat) (halt : a < 3 ^ ℓ)
    (h : ctmPow ℓ hℓ k = ctmPow ℓ hℓ a) : k % 3 ^ ℓ = a := by
  have hmod : ctmPow ℓ hℓ k = ctmPow ℓ hℓ (k % 3 ^ ℓ) := ctm_pow_mod ℓ hℓ k
  have hpos : 0 < 3 ^ ℓ := by have := zpu_pow_pos ℓ; omega
  have hmlt : k % 3 ^ ℓ < 3 ^ ℓ := Nat.mod_lt k hpos
  cases Nat.decEq (k % 3 ^ ℓ) a with
  | isTrue hh => exact hh
  | isFalse hh =>
    exact absurd (hmod.symm.trans h)
      (ctm_powers_distinct ℓ hℓ (k % 3 ^ ℓ) a hmlt halt hh)

/-! ## CCI-2: 指標の積公式（★M4a の新規数学） -/

/-- **CCI-2: char(σ·τ) = char σ · char τ mod 3^ℓ**（★ロードマップ §4.3 の欠落）。
    Gal の積は `fieldAutComp`（先 τ・次 σ）ゆえ (σ·τ)(ζ) = σ(τ ζ) = σ(ζ^b) = ζ^{a·b}
    （`ctr_charG_spec` ＋ `ctr_sigma_powG`）。一方 (σ·τ)(ζ) = ζ^{char(σ·τ)} で、
    char(σ·τ) < 3^ℓ（`ctr_charG_lt`）ゆえ `cci_indexG` で char(σ·τ) = a·b mod 3^ℓ。
    subgroupGrp の mul の val が `fieldAutComp σ.val τ.val` に defeq であることを
    冒頭 `show` で固定する。 -/
theorem cci_charG_mul (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ τ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) :
    ctr_charG ℓ hℓ ((galoisGroupGrp (cteExt ℓ hℓ)).mul σ τ).val
      = ctr_charG ℓ hℓ σ.val * ctr_charG ℓ hℓ τ.val % 3 ^ ℓ := by
  show ctr_charG ℓ hℓ (fieldAutComp σ.val τ.val)
      = ctr_charG ℓ hℓ σ.val * ctr_charG ℓ hℓ τ.val % 3 ^ ℓ
  -- (σ·τ)(ζ) = ζ^{a·b}
  have e2 : (fieldAutComp σ.val τ.val).toFun (ctmZeta ℓ hℓ)
      = ctmPow ℓ hℓ (ctr_charG ℓ hℓ σ.val * ctr_charG ℓ hℓ τ.val) := by
    show σ.val.toFun (τ.val.toFun (ctmZeta ℓ hℓ))
      = ctmPow ℓ hℓ (ctr_charG ℓ hℓ σ.val * ctr_charG ℓ hℓ τ.val)
    rw [ctr_charG_spec ℓ hℓ τ.val, ctr_sigma_powG ℓ hℓ σ.val (ctr_charG ℓ hℓ τ.val)]
  -- (σ·τ)(ζ) = ζ^{char(σ·τ)}
  have e1 : (fieldAutComp σ.val τ.val).toFun (ctmZeta ℓ hℓ)
      = ctmPow ℓ hℓ (ctr_charG ℓ hℓ (fieldAutComp σ.val τ.val)) :=
    ctr_charG_spec ℓ hℓ (fieldAutComp σ.val τ.val)
  have h : ctmPow ℓ hℓ (ctr_charG ℓ hℓ σ.val * ctr_charG ℓ hℓ τ.val)
      = ctmPow ℓ hℓ (ctr_charG ℓ hℓ (fieldAutComp σ.val τ.val)) := by rw [← e2, e1]
  exact (cci_indexG ℓ hℓ (ctr_charG ℓ hℓ σ.val * ctr_charG ℓ hℓ τ.val)
    (ctr_charG ℓ hℓ (fieldAutComp σ.val τ.val))
    (ctr_charG_lt ℓ hℓ (fieldAutComp σ.val τ.val)) h).symm

/-! ## CCI-3: 指標方向の群準同型 χ_ℓ -/

/-- **CCI-3: χ_ℓ : Gal(ℚ(ζ_{3^ℓ})/ℚ) → (ℤ/3^ℓ)^×** — σ ↦ char σ。map_mul は
    `cci_charG_mul`（担体は Subtype.ext で val 比較）。 -/
def cciToUnits (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    Hom (galoisGroupGrp (cteExt ℓ hℓ)) (zpuGrp ℓ hℓ) where
  map := fun σ => ⟨ctr_charG ℓ hℓ σ.val, ctr_charG_lt ℓ hℓ σ.val, ctr_charG_nd3 ℓ hℓ σ.val⟩
  map_mul := fun σ τ => Subtype.ext (cci_charG_mul ℓ hℓ σ τ)

/-! ## CCI-4: 逆方向 σ_a（代入自己同型・逆元 witness は zpuInvL） -/

/-- **CCI-4a: σ_a**（代入自己同型・逆元 witness は `zpuInvL`・choice-free）。 -/
def cciAut (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : (zpuGrp ℓ hℓ).carrier) : FieldAut (cteField ℓ hℓ) :=
  csaAut ℓ hℓ a.val (zpuInvL ℓ a.val) a.property.2
    (zpuInvL_nd3 ℓ hℓ a.val a.property.2) (zpuInvL_one ℓ hℓ a.val a.property.2)

/-- **CCI-4b: σ_a ∈ Gal(ℚ(ζ_{3^ℓ})/ℚ)**（ℚ 各点固定）。 -/
theorem cciAut_mem (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : (zpuGrp ℓ hℓ).carrier) :
    (galoisSubgroup (cteExt ℓ hℓ)).mem (cciAut ℓ hℓ a) :=
  csaAut_mem ℓ hℓ a.val (zpuInvL ℓ a.val) a.property.2
    (zpuInvL_nd3 ℓ hℓ a.val a.property.2) (zpuInvL_one ℓ hℓ a.val a.property.2)

/-- **CCI-4c: σ_a(ζ) = ζ^a**（`csaAut_zeta` の cci ラッパ）。 -/
theorem cci_aut_zeta (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : (zpuGrp ℓ hℓ).carrier) :
    (cciAut ℓ hℓ a).toFun (ctmZeta ℓ hℓ) = ctmPow ℓ hℓ a.val :=
  csaAut_zeta ℓ hℓ a.val (zpuInvL ℓ a.val) a.property.2
    (zpuInvL_nd3 ℓ hℓ a.val a.property.2) (zpuInvL_one ℓ hℓ a.val a.property.2)

/-- **CCI-4d: char(σ_a) = a**（右逆の核・§3.2 compat でも独立に使う）。
    σ_a(ζ) = ζ^a = ζ^{char σ_a}、両者 < 3^ℓ で `cci_indexG` ＋ `Nat.mod_eq_of_lt`。 -/
theorem cci_charG_csaAut (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : (zpuGrp ℓ hℓ).carrier) :
    ctr_charG ℓ hℓ (cciAut ℓ hℓ a) = a.val := by
  have hz : (cciAut ℓ hℓ a).toFun (ctmZeta ℓ hℓ) = ctmPow ℓ hℓ a.val := cci_aut_zeta ℓ hℓ a
  have hspec : (cciAut ℓ hℓ a).toFun (ctmZeta ℓ hℓ)
      = ctmPow ℓ hℓ (ctr_charG ℓ hℓ (cciAut ℓ hℓ a)) := ctr_charG_spec ℓ hℓ (cciAut ℓ hℓ a)
  have h : ctmPow ℓ hℓ a.val = ctmPow ℓ hℓ (ctr_charG ℓ hℓ (cciAut ℓ hℓ a)) := by rw [← hz, hspec]
  have hidx := cci_indexG ℓ hℓ a.val (ctr_charG ℓ hℓ (cciAut ℓ hℓ a))
    (ctr_charG_lt ℓ hℓ (cciAut ℓ hℓ a)) h
  rw [Nat.mod_eq_of_lt a.property.1] at hidx
  exact hidx.symm

/-- **CCI-4e: σ_a 方向の群準同型 (ℤ/3^ℓ)^× → Gal(ℚ(ζ_{3^ℓ})/ℚ)** — a ↦ σ_a。
    map_mul は `cae_aut_ext` の生成元一点比較: σ_{ab%3^ℓ}(ζ) = ζ^{ab%3^ℓ} = ζ^{ab}
    （`ctm_pow_mod`）、(σ_a·σ_b)(ζ) = σ_a(ζ^b) = ζ^{ab}（`cci_aut_zeta`＋
    `ctr_sigma_powG`＋`cci_charG_csaAut`）。 -/
def cciFromUnits (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    Hom (zpuGrp ℓ hℓ) (galoisGroupGrp (cteExt ℓ hℓ)) where
  map := fun a => ⟨cciAut ℓ hℓ a, cciAut_mem ℓ hℓ a⟩
  map_mul := fun a b => by
    apply Subtype.ext
    show cciAut ℓ hℓ ((zpuGrp ℓ hℓ).mul a b)
        = fieldAutComp (cciAut ℓ hℓ a) (cciAut ℓ hℓ b)
    refine cae_aut_ext ℓ hℓ (cciAut ℓ hℓ ((zpuGrp ℓ hℓ).mul a b))
      (fieldAutComp (cciAut ℓ hℓ a) (cciAut ℓ hℓ b))
      (cciAut_mem ℓ hℓ ((zpuGrp ℓ hℓ).mul a b))
      ((galoisSubgroup (cteExt ℓ hℓ)).mul_mem (cciAut_mem ℓ hℓ a) (cciAut_mem ℓ hℓ b)) ?_
    rw [csa_gen_eq ℓ hℓ]
    show (cciAut ℓ hℓ ((zpuGrp ℓ hℓ).mul a b)).toFun (ctmZeta ℓ hℓ)
        = (cciAut ℓ hℓ a).toFun ((cciAut ℓ hℓ b).toFun (ctmZeta ℓ hℓ))
    rw [cci_aut_zeta ℓ hℓ ((zpuGrp ℓ hℓ).mul a b), cci_aut_zeta ℓ hℓ b,
        ctr_sigma_powG ℓ hℓ (cciAut ℓ hℓ a) b.val, cci_charG_csaAut ℓ hℓ a]
    show ctmPow ℓ hℓ (a.val * b.val % 3 ^ ℓ) = ctmPow ℓ hℓ (a.val * b.val)
    exact (ctm_pow_mod ℓ hℓ (a.val * b.val)).symm

/-! ## CCI-5: 左右逆（同型の核） -/

/-- **CCI-5a: 左逆** σ_{char σ} = σ。`cae_aut_ext` の生成元一致
    σ_{char σ}(ζ) = ζ^{char σ} = σ(ζ)（`cci_aut_zeta` vs `ctr_charG_spec`）。 -/
theorem cci_left_inv (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) :
    (cciFromUnits ℓ hℓ).map ((cciToUnits ℓ hℓ).map σ) = σ := by
  apply Subtype.ext
  show cciAut ℓ hℓ ((cciToUnits ℓ hℓ).map σ) = σ.val
  refine cae_aut_ext ℓ hℓ (cciAut ℓ hℓ ((cciToUnits ℓ hℓ).map σ)) σ.val
    (cciAut_mem ℓ hℓ ((cciToUnits ℓ hℓ).map σ)) σ.property ?_
  rw [csa_gen_eq ℓ hℓ, cci_aut_zeta ℓ hℓ ((cciToUnits ℓ hℓ).map σ)]
  show ctmPow ℓ hℓ (ctr_charG ℓ hℓ σ.val) = σ.val.toFun (ctmZeta ℓ hℓ)
  exact (ctr_charG_spec ℓ hℓ σ.val).symm

/-- **CCI-5b: 右逆** char(σ_a) = a（`cci_charG_csaAut`・担体は Subtype.ext）。 -/
theorem cci_right_inv (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : (zpuGrp ℓ hℓ).carrier) :
    (cciToUnits ℓ hℓ).map ((cciFromUnits ℓ hℓ).map a) = a := by
  apply Subtype.ext
  show ctr_charG ℓ hℓ (cciAut ℓ hℓ a) = a.val
  exact cci_charG_csaAut ℓ hℓ a

/-! ## CCI-6: 同型レコード（GrpIso が無いので MuUnitsIsoData イディオム） -/

/-- **CCI-6a: レベル指標同型データ** Gal(ℚ(ζ_{3^ℓ})/ℚ) ≅ (ℤ/3^ℓ)^×
    （双方向 Hom ＋ 左右逆）。 -/
structure CciIsoData (ℓ : Nat) (hℓ : 1 ≤ ℓ) where
  /-- 指標方向 χ_ℓ : Gal → (ℤ/3^ℓ)^×。 -/
  toUnits : Hom (galoisGroupGrp (cteExt ℓ hℓ)) (zpuGrp ℓ hℓ)
  /-- σ_a 方向 (ℤ/3^ℓ)^× → Gal。 -/
  fromUnits : Hom (zpuGrp ℓ hℓ) (galoisGroupGrp (cteExt ℓ hℓ))
  /-- 左逆: σ_{char σ} = σ。 -/
  left_inv : ∀ σ, fromUnits.map (toUnits.map σ) = σ
  /-- 右逆: char(σ_a) = a。 -/
  right_inv : ∀ a, toUnits.map (fromUnits.map a) = a

/-- **CCI-6b: witness** — 全フィールド既証明の純レコード。 -/
def cciIsoData (ℓ : Nat) (hℓ : 1 ≤ ℓ) : CciIsoData ℓ hℓ where
  toUnits := cciToUnits ℓ hℓ
  fromUnits := cciFromUnits ℓ hℓ
  left_inv := cci_left_inv ℓ hℓ
  right_inv := cci_right_inv ℓ hℓ

/-- **CCI-6c: 同型の存在**（レベル ℓ の指標同型 Gal(ℚ(ζ_{3^ℓ})/ℚ) ≅ (ℤ/3^ℓ)^×）。 -/
theorem cciIso_exists (ℓ : Nat) (hℓ : 1 ≤ ℓ) : Nonempty (CciIsoData ℓ hℓ) :=
  ⟨cciIsoData ℓ hℓ⟩

/-! ## CCI-7: 円分切片の可換性（無償の系・非空虚性の見せ所） -/

/-- **CCI-7: Gal(ℚ(ζ_{3^ℓ})/ℚ) はアーベル** — σ·τ = τ·σ。`cae_aut_ext` の生成元一致
    ζ^{ab} = ζ^{ba}（`Nat.mul_comm`）。Kronecker–Weber 円分切片の可換性が本物に出る。 -/
theorem cci_gal_comm (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ τ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) :
    (galoisGroupGrp (cteExt ℓ hℓ)).mul σ τ = (galoisGroupGrp (cteExt ℓ hℓ)).mul τ σ := by
  apply Subtype.ext
  show fieldAutComp σ.val τ.val = fieldAutComp τ.val σ.val
  refine cae_aut_ext ℓ hℓ (fieldAutComp σ.val τ.val) (fieldAutComp τ.val σ.val)
    ((galoisSubgroup (cteExt ℓ hℓ)).mul_mem σ.property τ.property)
    ((galoisSubgroup (cteExt ℓ hℓ)).mul_mem τ.property σ.property) ?_
  rw [csa_gen_eq ℓ hℓ]
  show σ.val.toFun (τ.val.toFun (ctmZeta ℓ hℓ)) = τ.val.toFun (σ.val.toFun (ctmZeta ℓ hℓ))
  rw [ctr_charG_spec ℓ hℓ τ.val, ctr_sigma_powG ℓ hℓ σ.val (ctr_charG ℓ hℓ τ.val),
      ctr_charG_spec ℓ hℓ σ.val, ctr_sigma_powG ℓ hℓ τ.val (ctr_charG ℓ hℓ σ.val),
      Nat.mul_comm (ctr_charG ℓ hℓ σ.val) (ctr_charG ℓ hℓ τ.val)]

end IUT
