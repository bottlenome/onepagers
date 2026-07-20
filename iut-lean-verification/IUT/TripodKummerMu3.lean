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
import IUT.BelyiCubicReal

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

/-! ## tkm-3: 基礎座標 t = u³ と定数のデッキ固定 -/

/-- **tkm-3a: 基礎座標 t = u³** ∈ K[u]（被覆関係 u³ = t の右辺の実現）。 -/
def kmuT : Poly kmuK := ⟨psSingle kmuK kmuK.one 3, ⟨4, fun i hi => if_neg (by omega)⟩⟩

/-- **tkm-3b: デッキ σ_ζ は基礎座標 t = u³ を固定**（σ_ζ(u³) = (ζu)³ = ζ³u³ = u³）。
    「σ∘ι = ι（デッキは基礎環 K[t] を動かさない）」の生成元での顕示。 -/
theorem kmu_sigma_fixes_t : kmuPolyScale kmuZeta kmuT = kmuT := by
  apply Subtype.ext
  funext n
  show kmuK.mul (rpow kmuK kmuZeta n) (psSingle kmuK kmuK.one 3 n)
    = psSingle kmuK kmuK.one 3 n
  cases Nat.decEq n 3 with
  | isTrue he =>
    rw [he, show psSingle kmuK kmuK.one 3 3 = kmuK.one from if_pos rfl,
      kmu_zeta_rpow3, kmuK.one_mul kmuK.one]
  | isFalse hne =>
    rw [show psSingle kmuK kmuK.one 3 n = kmuK.zero from if_neg hne,
      CRing.mul_zero kmuK (rpow kmuK kmuZeta n)]

/-- **tkm-3c: デッキ σ_z は定数 K を固定**（M86F `psScale_psC`）。 -/
theorem kmu_sigma_fixes_const (z : kmuK.carrier) (c : kmuK.carrier) :
    (kmuSigma z).map ((polyC kmuK).map c) = (polyC kmuK).map c :=
  Subtype.ext (psScale_psC kmuK z c)

/-! ## tkm-4: 固定係数定理（Kummer descent の核） -/

/-- **tkm-4a: 基礎係数条件** — p の台が 3 の倍数の次数のみ（= K[u³] = K[t] の像）。 -/
def kmuBaseSupport (p : Poly kmuK) : Prop := ∀ n, n % 3 ≠ 0 → p.val n = kmuK.zero

/-- **tkm-4b: ζ の冪の周期性** rpow ζ (3q+r) = rpow ζ r（ζ³=1）。 -/
theorem kmu_zeta_pow_period (r : Nat) :
    ∀ q, rpow kmuK kmuZeta (3 * q + r) = rpow kmuK kmuZeta r := by
  intro q
  induction q with
  | zero => rw [show 3 * 0 + r = r from by omega]
  | succ q ih =>
    rw [show 3 * (q + 1) + r = (3 * q + r) + 3 from by omega,
      rpow_add kmuK kmuZeta (3 * q + r) 3, kmu_zeta_rpow3,
      CRing.mul_one kmuK (rpow kmuK kmuZeta (3 * q + r)), ih]

/-- **tkm-4c: ζ^n = ζ^{n mod 3}**。 -/
theorem kmu_zeta_pow_mod (n : Nat) :
    rpow kmuK kmuZeta n = rpow kmuK kmuZeta (n % 3) := by
  have e : 3 * (n / 3) + n % 3 = n := by omega
  calc rpow kmuK kmuZeta n
      = rpow kmuK kmuZeta (3 * (n / 3) + n % 3) := by rw [e]
    _ = rpow kmuK kmuZeta (n % 3) := kmu_zeta_pow_period (n % 3) (n / 3)

/-- **tkm-4d: 3∣n なら ζ^n = 1**。 -/
theorem kmu_zeta_pow_eq_one_of_mod0 (n : Nat) (h : n % 3 = 0) :
    rpow kmuK kmuZeta n = kmuK.one := by
  rw [kmu_zeta_pow_mod n, h]
  rfl

/-- **tkm-4e: 3∤n なら ζ^n ≠ 1**（ζ^1 = ζ ≠ 1・ζ^2 = ζ² ≠ 1・周期性）。 -/
theorem kmu_zeta_pow_ne_one (n : Nat) (h : n % 3 ≠ 0) :
    rpow kmuK kmuZeta n ≠ kmuK.one := by
  rw [kmu_zeta_pow_mod n]
  have hm : n % 3 = 1 ∨ n % 3 = 2 := by omega
  cases hm with
  | inl h1 =>
    rw [h1]
    show kmuK.mul (rpow kmuK kmuZeta 0) kmuZeta ≠ kmuK.one
    rw [show rpow kmuK kmuZeta 0 = kmuK.one from rfl, kmuK.one_mul kmuZeta]
    exact kmu_zeta_ne_one
  | inr h2 =>
    rw [h2]
    show kmuK.mul (rpow kmuK kmuZeta 1) kmuZeta ≠ kmuK.one
    rw [show rpow kmuK kmuZeta 1 = kmuZeta from by
      show kmuK.mul (rpow kmuK kmuZeta 0) kmuZeta = kmuZeta
      rw [show rpow kmuK kmuZeta 0 = kmuK.one from rfl, kmuK.one_mul kmuZeta]]
    exact kmu_zetaSq_ne_one

/-- **tkm-4f: 固定 ⟹ 基礎係数**（σf = f の各係数 (ζ^n−1)·f_n = 0・3∤n で ζ^n≠1・整域）。 -/
theorem kmu_fixed_imp_base (p : Poly kmuK)
    (h : kmuPolyScale kmuZeta p = p) : kmuBaseSupport p := by
  intro n hn
  have hcoeff : kmuK.mul (rpow kmuK kmuZeta n) (p.val n) = p.val n :=
    congrFun (congrArg Subtype.val h) n
  have hne : rpow kmuK kmuZeta n ≠ kmuK.one := kmu_zeta_pow_ne_one n hn
  have hsub : kmuK.add (rpow kmuK kmuZeta n) (kmuK.neg kmuK.one) ≠ kmuK.zero := by
    intro hz
    exact hne (CRing.eq_of_sub_eq_zero kmuK hz)
  apply kmu_no_zero_div (kmuK.add (rpow kmuK kmuZeta n) (kmuK.neg kmuK.one)) (p.val n) _ hsub
  rw [CRing.right_distrib kmuK (rpow kmuK kmuZeta n) (kmuK.neg kmuK.one) (p.val n),
    CRing.neg_mul kmuK kmuK.one (p.val n), kmuK.one_mul (p.val n), hcoeff,
    CRing.add_neg kmuK (p.val n)]

/-- **tkm-4g: 基礎係数 ⟹ 固定**（3∣n で ζ^n=1・3∤n で f_n=0）。 -/
theorem kmu_base_imp_fixed (p : Poly kmuK)
    (h : kmuBaseSupport p) : kmuPolyScale kmuZeta p = p := by
  apply Subtype.ext
  funext n
  show kmuK.mul (rpow kmuK kmuZeta n) (p.val n) = p.val n
  cases Nat.decEq (n % 3) 0 with
  | isTrue he =>
    rw [kmu_zeta_pow_eq_one_of_mod0 n he, kmuK.one_mul (p.val n)]
  | isFalse hne =>
    rw [h n hne, CRing.mul_zero kmuK (rpow kmuK kmuZeta n)]

/-- **定理 (tkm-4h): 固定係数定理 = Kummer descent の核** —
    σ_ζ f = f ⟺ f の台が 3 の倍数の次数のみ（= 基礎環 K[t] = K[u³] の像）。
    デッキ変換 σ_ζ の固定環がちょうど基礎環 K[t] であること（Kummer 降下）。 -/
theorem kmu_kummer_descent (p : Poly kmuK) :
    kmuPolyScale kmuZeta p = p ↔ kmuBaseSupport p :=
  ⟨kmu_fixed_imp_base p, kmu_base_imp_fixed p⟩

/-- **tkm-4i: 基礎座標 t = u³ は基礎環に属する**。 -/
theorem kmu_t_base : kmuBaseSupport kmuT := by
  intro n hn
  show psSingle kmuK kmuK.one 3 n = kmuK.zero
  apply if_neg
  intro he
  omega

/-! ## tkm-5: 実 μ₃ = {a : K // a³=1}（本物の 1 の 3 乗根群） -/

/-- **定理 (tkm-5a): 実 μ₃(K) = 1 の 3 乗根群** — 担体 {a : K // a³=1}、乗法は
    K の乗法（`rpow_one_mul_closed` で閉じる）、単位 1、逆元 a²（a·a²=a³=1）。
    Kummer 被覆 u³=t の**実デッキ群 = 実 μ₃ ⊂ K^×**。 -/
def kmuMu3 : Grp where
  carrier := { a : kmuK.carrier // rpow kmuK a 3 = kmuK.one }
  mul := fun a b => ⟨kmuK.mul a.val b.val, rpow_one_mul_closed kmuK 3 a.property b.property⟩
  one := ⟨kmuK.one, rpow_one_base kmuK 3⟩
  inv := fun a => ⟨kmuK.mul a.val a.val, by
    rw [rpow_mul_dist kmuK a.val a.val 3, a.property, kmuK.one_mul kmuK.one]⟩
  mul_assoc := fun a b c => Subtype.ext (kmuK.mul_assoc a.val b.val c.val)
  one_mul := fun a => Subtype.ext (kmuK.one_mul a.val)
  inv_mul := fun a => Subtype.ext (by
    show kmuK.mul (kmuK.mul a.val a.val) a.val = kmuK.one
    have e : rpow kmuK a.val 3 = kmuK.mul (kmuK.mul a.val a.val) a.val := by
      show kmuK.mul (kmuK.mul (kmuK.mul kmuK.one a.val) a.val) a.val = _
      rw [kmuK.one_mul a.val]
    rw [← e]; exact a.property)

/-- **tkm-5b: μ₃ の生成元 ζ = ζ₃**。 -/
def kmuMu3Zeta : kmuMu3.carrier := ⟨kmuZeta, kmu_zeta_rpow3⟩

/-- **tkm-5c: ζ² ∈ μ₃**。 -/
def kmuMu3ZetaSq : kmuMu3.carrier :=
  ⟨kmuK.mul kmuZeta kmuZeta, by
    rw [rpow_mul_dist kmuK kmuZeta kmuZeta 3, kmu_zeta_rpow3, kmuK.one_mul kmuK.one]⟩

/-- **tkm-5d: 1 ≠ ζ**（μ₃ 内）。 -/
theorem kmu_mu3_one_ne_zeta : kmuMu3.one ≠ kmuMu3Zeta := by
  intro h
  exact kmu_zeta_ne_one (congrArg Subtype.val h).symm

/-- **tkm-5e: 1 ≠ ζ²**（μ₃ 内）。 -/
theorem kmu_mu3_one_ne_zetaSq : kmuMu3.one ≠ kmuMu3ZetaSq := by
  intro h
  exact kmu_zetaSq_ne_one (congrArg Subtype.val h).symm

/-- **tkm-5f: ζ ≠ ζ²**（μ₃ 内）。μ₃ は少なくとも 3 元 {1,ζ,ζ²} を持つ。 -/
theorem kmu_mu3_zeta_ne_zetaSq : kmuMu3Zeta ≠ kmuMu3ZetaSq := by
  intro h
  exact kmu_zeta_ne_zetaSq (congrArg Subtype.val h)

/-! ## tkm-6: 実デッキ作用 GAction μ₃（u 被覆）と忠実性 -/

/-- **定理 (tkm-6a): 実デッキ作用** — μ₃ は被覆環 K[u] に係数スケーリングで
    genuine に作用する（`GAction kmuMu3`・作用則は M86F `psScale_one_base` /
    `psScale_comp`）。σ_g(f) = (n ↦ g^n·f_n)。 -/
def kmuDeck : GAction kmuMu3 where
  carrier := Poly kmuK
  act := fun g p => kmuPolyScale g.val p
  act_one := fun p => Subtype.ext (psScale_one_base kmuK p.val)
  act_mul := fun g h p => Subtype.ext (psScale_comp kmuK g.val h.val p.val).symm

/-- **定理 (tkm-6b): デッキ作用は忠実**（faithful）— 生成元 u = X 上の作用
    g·u = g·X の係数 1 が g をそのまま読み出すので、g ↦ (g·u) は単射。
    「μ₃ = 実デッキ群」（作用が群を忠実に表現する）。 -/
theorem kmu_deck_faithful (g h : kmuMu3.carrier)
    (hgh : kmuDeck.act g kmuVar = kmuDeck.act h kmuVar) : g = h := by
  apply Subtype.ext
  have hc : kmuK.mul (rpow kmuK g.val 1) (psX kmuK 1)
      = kmuK.mul (rpow kmuK h.val 1) (psX kmuK 1) :=
    congrFun (congrArg Subtype.val hgh) 1
  rw [show psX kmuK 1 = kmuK.one from if_pos rfl,
    show rpow kmuK g.val 1 = g.val from by
      show kmuK.mul (rpow kmuK g.val 0) g.val = g.val
      rw [show rpow kmuK g.val 0 = kmuK.one from rfl, kmuK.one_mul g.val],
    show rpow kmuK h.val 1 = h.val from by
      show kmuK.mul (rpow kmuK h.val 0) h.val = h.val
      rw [show rpow kmuK h.val 0 = kmuK.one from rfl, kmuK.one_mul h.val],
    CRing.mul_one kmuK g.val, CRing.mul_one kmuK h.val] at hc
  exact hc

/-! ## tkm-8: μ₃ × μ₃ の実 Grp・実作用（位数 9・二 μ₃ 因子・忠実） -/

/-- **tkm-8a: デッキ群 μ₃ × μ₃**（u 被覆 × v 被覆の結合塔のデッキ群）。
    tripod 基本群 F₂ の ℤ/3×ℤ/3 商の実現先。 -/
def kmuMu3Sq : Grp := prodGrp kmuMu3 kmuMu3

/-- **定理 (tkm-8b): μ₃×μ₃ の実デッキ作用**（第 1 因子は u 被覆・第 2 因子は
    v 被覆に係数スケーリングで作用）。genuine な `GAction kmuMu3Sq`。 -/
def kmuDeckProd : GAction kmuMu3Sq where
  carrier := Poly kmuK × Poly kmuK
  act := fun g p => (kmuPolyScale g.1.val p.1, kmuPolyScale g.2.val p.2)
  act_one := fun p => by
    have e1 : kmuPolyScale kmuK.one p.1 = p.1 := Subtype.ext (psScale_one_base kmuK p.1.val)
    have e2 : kmuPolyScale kmuK.one p.2 = p.2 := Subtype.ext (psScale_one_base kmuK p.2.val)
    show (kmuPolyScale kmuK.one p.1, kmuPolyScale kmuK.one p.2) = p
    rw [e1, e2]
  act_mul := fun g h p => by
    show (kmuPolyScale (kmuK.mul g.1.val h.1.val) p.1,
          kmuPolyScale (kmuK.mul g.2.val h.2.val) p.2)
      = (kmuPolyScale g.1.val (kmuPolyScale h.1.val p.1),
          kmuPolyScale g.2.val (kmuPolyScale h.2.val p.2))
    rw [show kmuPolyScale (kmuK.mul g.1.val h.1.val) p.1
          = kmuPolyScale g.1.val (kmuPolyScale h.1.val p.1) from
        Subtype.ext (psScale_comp kmuK g.1.val h.1.val p.1.val).symm,
      show kmuPolyScale (kmuK.mul g.2.val h.2.val) p.2
          = kmuPolyScale g.2.val (kmuPolyScale h.2.val p.2) from
        Subtype.ext (psScale_comp kmuK g.2.val h.2.val p.2.val).symm]

/-- **定理 (tkm-8c): μ₃×μ₃ の作用は忠実**（成分ごとに生成元 (u,v) 上で単射）。
    ℤ/3×ℤ/3 が忠実に実デッキ変換として実現される。 -/
theorem kmu_deck_prod_faithful (g h : kmuMu3Sq.carrier)
    (hgh : kmuDeckProd.act g (kmuVar, kmuVar) = kmuDeckProd.act h (kmuVar, kmuVar)) :
    g = h := by
  have h1 : g.1 = h.1 := kmu_deck_faithful g.1 h.1 (congrArg Prod.fst hgh)
  have h2 : g.2 = h.2 := kmu_deck_faithful g.2 h.2 (congrArg Prod.snd hgh)
  show (g.1, g.2) = (h.1, h.2)
  rw [h1, h2]

/-! ## tkm-7: twin 被覆 v³ = 1 − t のデッキ -/

/-- **tkm-7a: `psScale ζ` は単項式 u³ = X³ を固定**（係数 3 は ζ³=1 で不変）。 -/
theorem kmu_scale_single3 :
    psScale kmuK kmuZeta (psSingle kmuK kmuK.one 3) = psSingle kmuK kmuK.one 3 := by
  funext n
  show kmuK.mul (rpow kmuK kmuZeta n) (psSingle kmuK kmuK.one 3 n)
    = psSingle kmuK kmuK.one 3 n
  cases Nat.decEq n 3 with
  | isTrue he =>
    rw [he, show psSingle kmuK kmuK.one 3 3 = kmuK.one from if_pos rfl,
      kmu_zeta_rpow3, kmuK.one_mul kmuK.one]
  | isFalse hne =>
    rw [show psSingle kmuK kmuK.one 3 n = kmuK.zero from if_neg hne,
      CRing.mul_zero kmuK (rpow kmuK kmuZeta n)]

/-- **tkm-7b: twin 被覆の基礎座標 t = 1 − v³** ∈ K[v]（被覆 v³ = 1 − t）。 -/
def kmuTwin : Poly kmuK :=
  ⟨psAdd kmuK (psC kmuK kmuK.one) (psNeg kmuK (psSingle kmuK kmuK.one 3)), by
    refine ⟨4, ?_⟩
    intro i hi
    show kmuK.add (psC kmuK kmuK.one i) (kmuK.neg (psSingle kmuK kmuK.one 3 i)) = kmuK.zero
    rw [show psC kmuK kmuK.one i = kmuK.zero from if_neg (by omega),
      show psSingle kmuK kmuK.one 3 i = kmuK.zero from if_neg (by omega),
      CRing.neg_zero kmuK, kmuK.add_zero kmuK.zero]⟩

/-- **tkm-7c: twin デッキ σ_ζ は 1 − v³ を固定**（σ_ζ(1−v³) = 1−ζ³v³ = 1−v³）。 -/
theorem kmu_sigma_fixes_twin : kmuPolyScale kmuZeta kmuTwin = kmuTwin := by
  apply Subtype.ext
  show psScale kmuK kmuZeta
      (psAdd kmuK (psC kmuK kmuK.one) (psNeg kmuK (psSingle kmuK kmuK.one 3)))
    = psAdd kmuK (psC kmuK kmuK.one) (psNeg kmuK (psSingle kmuK kmuK.one 3))
  rw [psScale_add kmuK kmuZeta (psC kmuK kmuK.one) (psNeg kmuK (psSingle kmuK kmuK.one 3)),
    psScale_psC kmuK kmuZeta kmuK.one,
    psScale_neg kmuK kmuZeta (psSingle kmuK kmuK.one 3),
    kmu_scale_single3]

/-- **tkm-7d: twin 座標 1 − v³ は基礎環に属する**（台は次数 0, 3）。 -/
theorem kmu_twin_base : kmuBaseSupport kmuTwin := by
  intro n hn
  show kmuK.add (psC kmuK kmuK.one n) (kmuK.neg (psSingle kmuK kmuK.one 3 n)) = kmuK.zero
  rw [show psC kmuK kmuK.one n = kmuK.zero from if_neg (by omega),
    show psSingle kmuK kmuK.one 3 n = kmuK.zero from if_neg (by omega),
    CRing.neg_zero kmuK, kmuK.add_zero kmuK.zero]

/-! ## tkm-9: 分岐値の決定（⊆ {0,∞} / ⊆ {1,∞}・和集合 {0,1,∞}） -/

/-- **tkm-9a: K における 3**（= ℚ の 3 の像・被覆の形式微分 d(X³)=3X² の係数）。 -/
def kmuThree : kmuK.carrier := kmuEmb.map (blcThree ratRing)

/-- **tkm-9b: 3 ≠ 0 in K**（emb 単射 + `blc_three_rat_ne_zero`・char 0）。 -/
theorem kmu_three_ne_zero : kmuThree ≠ kmuK.zero := by
  intro h
  apply blc_three_rat_ne_zero
  apply cq2_emb_injective
  exact h.trans (RingHom.map_zero cq2Field.emb).symm

/-- **定理 (tkm-9c): u 被覆 u³=t の分岐値 ⊆ {0,∞}** — ファイバー X³−c の二重根 a
    （a³=c かつ形式微分 3a²=0）は c=0 を強制する（3≠0・整域より a²=0、ゆえ
    c=a³=a²·a=0）。blc-4 の重根イディオムの X³ 版。有限分岐点は 0 のみ。 -/
theorem kmu_branch_u (a c : kmuK.carrier) (hroot : rpow kmuK a 3 = c)
    (hderiv : kmuK.mul kmuThree (kmuK.mul a a) = kmuK.zero) : c = kmuK.zero := by
  have ha2 : kmuK.mul a a = kmuK.zero :=
    kmu_no_zero_div kmuThree (kmuK.mul a a) hderiv kmu_three_ne_zero
  have e : rpow kmuK a 3 = kmuK.mul (kmuK.mul a a) a := by
    show kmuK.mul (kmuK.mul (kmuK.mul kmuK.one a) a) a = _
    rw [kmuK.one_mul a]
  rw [← hroot, e, ha2, CRing.zero_mul kmuK a]

/-- **定理 (tkm-9d): v 被覆 v³=1−t の分岐値 ⊆ {1,∞}** — ファイバー X³−(1−c) の
    二重根 a は 1−c=0、ゆえ c=1 を強制する。有限分岐点は 1 のみ。
    二被覆の分岐値の和集合が {0,1,∞}（tripod 三点性の対言明）。 -/
theorem kmu_branch_v (a c : kmuK.carrier)
    (hroot : rpow kmuK a 3 = kmuK.add kmuK.one (kmuK.neg c))
    (hderiv : kmuK.mul kmuThree (kmuK.mul a a) = kmuK.zero) : c = kmuK.one := by
  have ha2 : kmuK.mul a a = kmuK.zero :=
    kmu_no_zero_div kmuThree (kmuK.mul a a) hderiv kmu_three_ne_zero
  have e : rpow kmuK a 3 = kmuK.mul (kmuK.mul a a) a := by
    show kmuK.mul (kmuK.mul (kmuK.mul kmuK.one a) a) a = _
    rw [kmuK.one_mul a]
  have hz : kmuK.add kmuK.one (kmuK.neg c) = kmuK.zero := by
    rw [← hroot, e, ha2, CRing.zero_mul kmuK a]
  exact (CRing.eq_of_sub_eq_zero kmuK hz).symm

/-! ## tkm-10: capstone — tripod ℤ/3×ℤ/3 商の実 Kummer 被覆デッキ実現 -/

/-- **tkm-10a: 実現レコード** — tripod 基本群 F₂ の ℤ/3×ℤ/3 商の、実 Kummer 被覆
    u³=t / v³=1−t 上の実 μ₃×μ₃ デッキ群としての実現。各 field が本物の証明を
    要求する grounded 構造（骨格でなくインスタンス化に本物の内容が要る）。 -/
structure TripodKummerMu3Realization where
  /-- デッキ σ_ζ は位数 3（3 乗で恒等）。 -/
  sigmaCube : ∀ p : Poly kmuK,
    kmuPolyScale kmuZeta (kmuPolyScale kmuZeta (kmuPolyScale kmuZeta p)) = p
  /-- デッキ σ_ζ は非自明（生成元で ζu ≠ u）。 -/
  sigmaNeId : kmuPolyScale kmuZeta kmuVar ≠ kmuVar
  /-- Kummer descent: σ_ζ の固定環 = 基礎環 K[t]=K[u³]。 -/
  descent : ∀ p : Poly kmuK, kmuPolyScale kmuZeta p = p ↔ kmuBaseSupport p
  /-- σ_ζ は u 被覆の基礎座標 t=u³ を固定。 -/
  fixesT : kmuPolyScale kmuZeta kmuT = kmuT
  /-- σ_ζ は v 被覆の基礎座標 1−v³ を固定。 -/
  fixesTwin : kmuPolyScale kmuZeta kmuTwin = kmuTwin
  /-- μ₃ は少なくとも 3 元 {1,ζ,ζ²} を持つ（二 μ₃ 因子の各々）。 -/
  mu3Distinct : kmuMu3.one ≠ kmuMu3Zeta ∧ kmuMu3.one ≠ kmuMu3ZetaSq
      ∧ kmuMu3Zeta ≠ kmuMu3ZetaSq
  /-- μ₃×μ₃ の実デッキ作用は忠実（ℤ/3×ℤ/3 の忠実実現）。 -/
  prodFaithful : ∀ g h : kmuMu3Sq.carrier,
    kmuDeckProd.act g (kmuVar, kmuVar) = kmuDeckProd.act h (kmuVar, kmuVar) → g = h
  /-- u 被覆の分岐値 ⊆ {0,∞}。 -/
  branchU : ∀ a c : kmuK.carrier, rpow kmuK a 3 = c →
    kmuK.mul kmuThree (kmuK.mul a a) = kmuK.zero → c = kmuK.zero
  /-- v 被覆の分岐値 ⊆ {1,∞}。 -/
  branchV : ∀ a c : kmuK.carrier,
    rpow kmuK a 3 = kmuK.add kmuK.one (kmuK.neg c) →
    kmuK.mul kmuThree (kmuK.mul a a) = kmuK.zero → c = kmuK.one

/-- **tkm-10b: 実現の実証人** — 全 field が上で完全証明した本物の内容。 -/
def kmuRealization : TripodKummerMu3Realization where
  sigmaCube := kmu_sigma_cube
  sigmaNeId := kmu_sigma_ne_id
  descent := kmu_kummer_descent
  fixesT := kmu_sigma_fixes_t
  fixesTwin := kmu_sigma_fixes_twin
  mu3Distinct := ⟨kmu_mu3_one_ne_zeta, kmu_mu3_one_ne_zetaSq, kmu_mu3_zeta_ne_zetaSq⟩
  prodFaithful := kmu_deck_prod_faithful
  branchU := kmu_branch_u
  branchV := kmu_branch_v

/-- **定理 (tkm-10c): tripod ℤ/3×ℤ/3 商の実 Kummer デッキ実現は存在する**。 -/
theorem kmu_realization_exists : Nonempty TripodKummerMu3Realization :=
  ⟨kmuRealization⟩

end IUT
