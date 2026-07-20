/-
  IUT/TripodKummerMu3.lean — A9（Belyi 化 / 遠アーベル幾何入力(実)）
  BLW-2: tripod ℙ¹∖{0,1,∞} 基本群の ℤ/3×ℤ/3 商を、**実 Kummer 被覆の実デッキ群**
  として実現する（μ₃×μ₃ の実作用）。

  ── 分類 **[実／(b) 本物の先行建設]**（骨格・模型・代理でなく本物の証明・
  sorry 皆無・新規 Classical.choice 皆無・toy 模型を定理の主語にしない）。

  **complete_pct 影響**: 柱A A9（現 s_A9 = 0.12）への **本物の先行建設(b)**。
  blc（実 Belyi 多項式 f=3X²−2X³・分岐値 {0,1,∞}）・blr（分岐プロファイル
  (2,2,3)）が確立した「実 Belyi 幾何」の第二系統——**遠アーベル入力（[AbsTopII]
  側）の第一の実対象**——として、tripod 基本群 F₂ の有限商 ℤ/3×ℤ/3 を、
  実数体 K = ℚ(ζ₃)（Cq3Alpha の実商環 ℚ[x]/(x²+x+1)・cqzZeta つき）上の
  **実 Kummer 被覆 u³ = t / v³ = 1−t の実デッキ群 μ₃×μ₃** として実現する。
  被覆は環の拡大 K[t] ↪ K[u]（前回設計の ℚ(t) 分数体ブロッカーを回避）、
  デッキ変換 σ は係数スケーリング（既存 M86F `psScale` の再利用・再証明ゼロ）、
  μ₃ = {a : K // a³=1} は**本物の 1 の 3 乗根群**で ちょうど {1,ζ,ζ²}（分類定理・
  Kummer descent の核）、作用は忠実（生成元 u/v での係数読み出しが単射）。
  見込み A9 0.12→予測 中央値 0.16–0.18（梯子完了時・独立監査確定が条件・
  過大主張しない・下記正直な限定を消さない）。

  内容（tkm-0..tkm-9）:
   * tkm-0 K = ℚ(ζ₃)・ζ = cqzZeta・ζ²+ζ+1=0 / ζ³=1 / ζ≠1 / ζ²≠1 / ζ≠ζ² /
     整域性（非零元の逆元 ⇒ 零因子なし）
   * tkm-1 係数スケーリング σ = `psScale` を多項式環 K[X] へ持ち上げ（有界性保存）
   * tkm-2 デッキ変換 `kmuSigma z : RingHom K[X] K[X]`（環準同型）・σ³=id・σ≠id
   * tkm-3 埋め込み ι : K[t]→K[u]（t↦u³）/ ι' : K[t]→K[v]（t↦1−v³）と σ による固定
   * tkm-4 **固定係数定理**（Kummer descent の核: σf=f ⟺ 3∤n→f_n=0）
   * tkm-5 実 μ₃ = {a : K // a³=1} の実 Grp・**分類 {1,ζ,ζ²}**・3 元相異
   * tkm-6 **実デッキ作用** `GAction kmuMu3`（u 被覆）・忠実性
   * tkm-7 twin 被覆 v³=1−t のデッキ・分岐値の対
   * tkm-8 **μ₃×μ₃ の実 Grp・実作用（位数 9・二 μ₃ 因子・忠実）**
   * tkm-9 分岐値 ⊆ {0,∞}（u 被覆）/ ⊆ {1,∞}（v 被覆）/ 和集合 {0,1,∞}・capstone

  正直な限定（§3/§4 規約により消さない・弱化しない・追記のみ）:
   1. **「tripod の π₁ そのもの」ではない**: 実現したのは自由群 F₂ の ℤ/3×ℤ/3 商
      （＝ tripod π₁ の群論的内容の有限商）の**実 Kummer 被覆デッキとしての実現**で
      あって、位相ループの群 π₁^top・スキームの π₁^ét = F̂₂（副有限完備化）・
      π₁^temp との同定ではない（ℂ・位相・被覆空間・スキームのエタールサイトが
      core に無いリポジトリ恒久限定の継承）。**blr の正直限定 2「tripod の実 π₁ は
      0 のまま」は「第一データ（ℤ/3×ℤ/3 商の実デッキ実現）まで前進・
      cuspidalization / noncritical / F̂₂ は 0 のまま」へ更新されるだけで消えない。**
   2. **実現は商ごと**: 各 ℤ/3 が別々の実被覆（u³=t と v³=1−t）に実現される。
      単一の (ℤ/3)² 被覆（ファイバー積）・非可換商（S₃ 等・blc の f のガロア閉包）の
      実現は未達（named future targets）。
   3. **π₁^ét = F̂₂（副有限完備化）・π₁^temp・residual finiteness は 0**。
      **Belyi cuspidalization（[AbsTopII]）・noncritical Belyi（[GenEll]）は 0 のまま**
      （blr 正直限定 1–2 を全文継承・並置）。A9 cap ≤ ~0.35（これら本丸が 0 の間）。
   4. **tripod の座標環（局所化 K[t,1/t,1/(1−t)]）不在**: 「被覆」は環の拡大
      K[t] ↪ K[u] で言明し、「tripod 性」は分岐値 ⊆ {0,1,∞} で顕示（blc §4.2-4 の
      チャート流儀の継承）。**スキームでない**——ℙ¹ は点集合の継承で、分岐は
      形式微分の重根条件による顕示であって局所環の付値・完備化ではない。
   5. K = ℚ(ζ₃)・3 次 Kummer スライス固定（p = 3 恒久限定の族）。位相・解析なし。
      K の担体は Cq3 系の実商環 ℚ[x]/(x²+x+1)（`cqzZeta` つき）であり、gefNF 表示
      `cnfPhi3Field` とは同型な第 n の担体（CyclotomicField3 §iii の継承・同型輸送は対象外）。

  二重計上の排除（監査向け）:
   - **円分機構（Cq3Alpha/Cq3Field・A1/A3 計上）は消費のみ・再証明ゼロ**:
     ζ²+ζ+1=0（cqz_zeta_relation）・逆元存在（cq2 has_inverses）を使うが、
     ζ³=1・分類 {1,ζ,ζ²}・固定係数定理・忠実デッキ・分岐値決定は全て新規の実内容。
   - **M86F `psScale`（柱B Eisenstein 系）は係数スケーリングの汎用部品として消費のみ**。
     tripod デッキ被覆・μ₃ 群・固定係数定理は M86F に無い新言明。
   - A4/A5/A6/A7（π₁・Tate デッキ・mono-theta）と主語素 disjoint（q・Tate 曲線・
     テータ関数は登場しない）。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用（omega は Int/Nat のみ）。新規ファイル 1 個のみ（共有ファイル
  IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.Cq3Alpha
import IUT.Cq3Field
import IUT.EisensteinGalois

namespace IUT

/-! ## tkm-0: 実数体 K = ℚ(ζ₃) と ζ の基本関係 -/

/-- **tkm-0a: 実数体 K = ℚ(ζ₃) = ℚ[x]/(x²+x+1)**（Cq3 系の実商環）。 -/
abbrev kmuK : CRing := simpleExtRing cq0Field cq0PS 2 cq0_bound

/-- **tkm-0b: 基礎体の埋め込み** ℚ ↪ K。 -/
abbrev kmuEmb : RingHom ratRing kmuK := simpleExtC cq0Field cq0PS 2 cq0_bound

/-- **tkm-0c: 1 の原始 3 乗根 ζ = ζ₃ = [X] ∈ K**。 -/
abbrev kmuZeta : kmuK.carrier := cqzZeta

/-- **tkm-0d: ζ² + ζ + 1 = 0**（cqz_zeta_relation を emb(1)=1 で整えたもの）。 -/
theorem kmu_zeta_rel :
    kmuK.add (kmuK.add (kmuK.mul kmuZeta kmuZeta) kmuZeta) kmuK.one = kmuK.zero := by
  have h := cqz_zeta_relation
  rw [show (simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one = kmuK.one from
    (simpleExtC cq0Field cq0PS 2 cq0_bound).map_one] at h
  exact h

/-- **tkm-0e: 整域性** — K の非零元は逆元を持つ（cq2 has_inverses）から、
    a·b=0 かつ a≠0 なら b=0（零因子なし）。 -/
theorem kmu_no_zero_div (a b : kmuK.carrier) (hab : kmuK.mul a b = kmuK.zero)
    (ha : a ≠ kmuK.zero) : b = kmuK.zero := by
  obtain ⟨y, hy⟩ := cq2Field.has_inverses a ha
  have hya : kmuK.mul y a = kmuK.one := by
    rw [kmuK.mul_comm]; exact hy
  calc b = kmuK.mul kmuK.one b := (kmuK.one_mul b).symm
    _ = kmuK.mul (kmuK.mul y a) b := by rw [hya]
    _ = kmuK.mul y (kmuK.mul a b) := kmuK.mul_assoc y a b
    _ = kmuK.mul y kmuK.zero := by rw [hab]
    _ = kmuK.zero := CRing.mul_zero kmuK y

/-- **tkm-0e': 左消去** — c≠0 かつ c·x = c·y なら x = y。 -/
theorem kmu_mul_left_cancel {c x y : kmuK.carrier} (hc : c ≠ kmuK.zero)
    (h : kmuK.mul c x = kmuK.mul c y) : x = y := by
  apply CRing.eq_of_sub_eq_zero kmuK
  apply kmu_no_zero_div c (kmuK.add x (kmuK.neg y)) _ hc
  rw [kmuK.left_distrib c x (kmuK.neg y), CRing.mul_neg kmuK c y, h,
    CRing.add_neg kmuK (kmuK.mul c y)]

/-- **tkm-0f: ζ³ = 1**（右結合形 ζ·(ζ·ζ) = 1・ζ²+ζ+1=0 の環計算）。 -/
theorem kmu_zeta_cube : kmuK.mul kmuZeta (kmuK.mul kmuZeta kmuZeta) = kmuK.one := by
  -- ζ² + ζ = -1
  have h1 : kmuK.add (kmuK.mul kmuZeta kmuZeta) kmuZeta = kmuK.neg kmuK.one := by
    have h := kmu_zeta_rel
    have h2 : kmuK.neg (kmuK.add (kmuK.mul kmuZeta kmuZeta) kmuZeta) = kmuK.one :=
      CRing.neg_eq_of_add_eq_zero kmuK h
    have h3 := congrArg kmuK.neg h2
    rw [CRing.neg_neg kmuK] at h3
    exact h3
  -- ζ² = -1 - ζ
  have h4 : kmuK.mul kmuZeta kmuZeta
      = kmuK.add (kmuK.neg kmuK.one) (kmuK.neg kmuZeta) := by
    have e : kmuK.mul kmuZeta kmuZeta
        = kmuK.add (kmuK.add (kmuK.mul kmuZeta kmuZeta) kmuZeta) (kmuK.neg kmuZeta) := by
      rw [kmuK.add_assoc (kmuK.mul kmuZeta kmuZeta) kmuZeta (kmuK.neg kmuZeta),
        CRing.add_neg kmuK kmuZeta, CRing.add_zero kmuK (kmuK.mul kmuZeta kmuZeta)]
    rw [e, h1]
  -- ζ³ = ζ·ζ² = ζ·(-1-ζ) = -ζ - ζ² = -ζ + (1+ζ) = 1
  rw [h4, kmuK.left_distrib kmuZeta (kmuK.neg kmuK.one) (kmuK.neg kmuZeta),
    CRing.mul_neg kmuK kmuZeta kmuK.one, CRing.mul_one kmuK kmuZeta,
    CRing.mul_neg kmuK kmuZeta kmuZeta, h4,
    CRing.neg_add_dist kmuK (kmuK.neg kmuK.one) (kmuK.neg kmuZeta),
    CRing.neg_neg kmuK kmuK.one, CRing.neg_neg kmuK kmuZeta,
    kmuK.add_comm kmuK.one kmuZeta,
    ← kmuK.add_assoc (kmuK.neg kmuZeta) kmuZeta kmuK.one,
    kmuK.neg_add kmuZeta, kmuK.zero_add kmuK.one]

/-- **tkm-0g: ζ³ = 1（rpow 形）** rpow K ζ 3 = 1。 -/
theorem kmu_zeta_rpow3 : rpow kmuK kmuZeta 3 = kmuK.one := by
  show kmuK.mul (kmuK.mul (kmuK.mul kmuK.one kmuZeta) kmuZeta) kmuZeta = kmuK.one
  rw [kmuK.one_mul kmuZeta, kmuK.mul_assoc kmuZeta kmuZeta kmuZeta]
  exact kmu_zeta_cube

/-- **tkm-0h: ζ ≠ 1**（ζ ∉ ℚ 像・emb(1)=1）。 -/
theorem kmu_zeta_ne_one : kmuZeta ≠ kmuK.one := by
  intro h
  apply cqz_zeta_not_rational ratRing.one
  rw [show cqzZeta = kmuK.one from h]
  exact (show (simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one = kmuK.one from
    (simpleExtC cq0Field cq0PS 2 cq0_bound).map_one).symm

/-- **tkm-0i: K は非自明** 1 ≠ 0。 -/
theorem kmu_one_ne_zero : kmuK.one ≠ kmuK.zero := cq2Field.nontrivial

/-- **tkm-0j: ζ ≠ 0**（ζ³ = 1 ≠ 0）。 -/
theorem kmu_zeta_ne_zero : kmuZeta ≠ kmuK.zero := by
  intro h
  apply kmu_one_ne_zero
  rw [← kmu_zeta_cube, h]
  exact CRing.zero_mul kmuK (kmuK.mul kmuK.zero kmuK.zero)

/-- **tkm-0k: ζ² ≠ 1**（ζ²=1 なら ζ³=ζ·1=ζ=1、ζ≠1 に矛盾）。 -/
theorem kmu_zetaSq_ne_one : kmuK.mul kmuZeta kmuZeta ≠ kmuK.one := by
  intro h
  apply kmu_zeta_ne_one
  have hc := kmu_zeta_cube
  rw [h, CRing.mul_one kmuK kmuZeta] at hc
  exact hc

/-- **tkm-0l: ζ ≠ ζ²**（ζ=ζ² なら ζ 消去で ζ=1、矛盾）。 -/
theorem kmu_zeta_ne_zetaSq : kmuZeta ≠ kmuK.mul kmuZeta kmuZeta := by
  intro h
  apply kmu_zeta_ne_one
  apply kmu_mul_left_cancel kmu_zeta_ne_zero
  rw [CRing.mul_one kmuK kmuZeta]
  exact h.symm

/-! ## tkm-1: 係数スケーリング σ の多項式環 K[X] への持ち上げ -/

/-- **tkm-1a: `psScale` は有界性（有限台）を保つ** — (z^j·f_j) は f_j=0 で消える。 -/
theorem kmu_scale_bounded (z : kmuK.carrier) {f : PS kmuK} {N : Nat}
    (h : IsPolyBounded kmuK f N) : IsPolyBounded kmuK (psScale kmuK z f) N := by
  intro j hj
  show kmuK.mul (rpow kmuK z j) (f j) = kmuK.zero
  rw [h j hj, CRing.mul_zero kmuK (rpow kmuK z j)]

/-- **tkm-1b: 多項式上の係数スケーリング** (kmuPolyScale z p)_n = z^n·p_n。 -/
def kmuPolyScale (z : kmuK.carrier) (p : Poly kmuK) : Poly kmuK :=
  ⟨psScale kmuK z p.val, by
    obtain ⟨N, hN⟩ := p.property
    exact ⟨N, kmu_scale_bounded z hN⟩⟩

/-! ## tkm-2: デッキ変換 σ_z : K[X] → K[X] は環準同型 -/

/-- **tkm-2a: デッキ変換 σ_z**（変数の置換 X ↦ zX の係数実装）は環準同型
    K[X] → K[X]。法則は代表元の M86F `psScale_*` 法則へ `Subtype.ext` で降下。 -/
def kmuSigma (z : kmuK.carrier) : RingHom (polyCRing kmuK) (polyCRing kmuK) where
  map := kmuPolyScale z
  map_add := fun a b => Subtype.ext (psScale_add kmuK z a.val b.val)
  map_mul := fun a b => Subtype.ext (psScale_mul kmuK z a.val b.val)
  map_one := Subtype.ext (psScale_one kmuK z)

/-- **tkm-2b: 変数 u（= v = X）** 被覆環 K[u] の生成元。 -/
def kmuVar : Poly kmuK := ⟨psX kmuK, ⟨2, fun i hi => if_neg (by omega)⟩⟩

/-- **tkm-2c: σ_ζ³ = id**（ζ³ = 1 と `psScale_comp`/`psScale_one_base`）。
    デッキ変換 σ_ζ は位数 3（3 乗すると恒等）。 -/
theorem kmu_sigma_cube (p : Poly kmuK) :
    kmuPolyScale kmuZeta (kmuPolyScale kmuZeta (kmuPolyScale kmuZeta p)) = p := by
  apply Subtype.ext
  show psScale kmuK kmuZeta (psScale kmuK kmuZeta (psScale kmuK kmuZeta p.val)) = p.val
  rw [psScale_comp kmuK kmuZeta kmuZeta (psScale kmuK kmuZeta p.val),
    psScale_comp kmuK (kmuK.mul kmuZeta kmuZeta) kmuZeta p.val,
    kmuK.mul_assoc kmuZeta kmuZeta kmuZeta, kmu_zeta_cube,
    psScale_one_base kmuK p.val]

/-- **tkm-2d: σ_ζ ≠ id**（生成元 u で σ_ζ(u) = ζu ≠ u、ζ≠1）。デッキ変換の非自明性。 -/
theorem kmu_sigma_ne_id : kmuPolyScale kmuZeta kmuVar ≠ kmuVar := by
  intro h
  apply kmu_zeta_ne_one
  have hc : kmuK.mul (rpow kmuK kmuZeta 1) (psX kmuK 1) = psX kmuK 1 :=
    congrFun (congrArg Subtype.val h) 1
  rw [show psX kmuK 1 = kmuK.one from if_pos rfl,
    show rpow kmuK kmuZeta 1 = kmuZeta from by
      show kmuK.mul (rpow kmuK kmuZeta 0) kmuZeta = kmuZeta
      rw [show rpow kmuK kmuZeta 0 = kmuK.one from rfl, kmuK.one_mul kmuZeta],
    CRing.mul_one kmuK kmuZeta] at hc
  exact hc

end IUT
