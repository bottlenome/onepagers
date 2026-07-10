/-
  IUT/CyclotomicRes39.lean — A3/W-C 最終段（CR39: 制限準同型
  res: Gal(ℚ(ζ₉)/ℚ) → Gal(ℚ(ζ₃)/ℚ) の本物構成）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実 2 段円分塔 ℚ(ζ₃) ⊂ ℚ(ζ₉) の上での**制限準同型 res の本物の構成**。
     指標 a := cm9Find(σ(x̄₉))（σ(x̄₉)⁹ = 1 の map 9 連鎖から抽出）で
     res(σ) := (a mod 3 = 1 なら id、さもなくば cg3Conj) と定め、
     意味論 compat（ι∘res(σ) = σ∘ι）と群準同型性（map_mul）を完全証明する。
     これは `ProfinitePi1Tower.restr` witness の初の本物 discharge の核）。

  complete_pct 影響: A3——**制限準同型 res: Gal(ℚ(ζ₉)/ℚ)→Gal(ℚ(ζ₃)/ℚ) の
  初の本物構成**（従来 witness 仮説だった restr を実 2 段円分塔で discharge）。
  円分塔 2 段＋res で A3 を前進させる本丸（独立監査で 0.55→0.6 を確定予定・
  本ファイル単体では complete_pct 未設定）。

  内容（設計 audit/A3-cyclotomic-tower-detail-2026-07-09.md §2.2 CR39）:
   * `cr39_rpow_hom`  — σ の冪保存 rpow(σ z) = σ(rpow z)（map_mul/map_one の帰納）。
   * `cr39_rpow_zeta` — rpow p9iPhi9Field cm9Zeta k = cm9Pow k（gefNFPow との同一視）。
   * `cr39_sigma_zeta9_pow9` — σ(x̄₉)⁹ = 1（map 9 連鎖 + cm9_zeta_pow9）。
   * `cr39Char`/`cr39_char_lt`/`cr39_char_spec` — 指標 a = cm9Find(σ x̄₉)（a<9・σ x̄₉ = x̄₉^a）。
   * `cr39_sigma_pow` — σ(x̄₉^k) = x̄₉^{a·k}。
   * `cr39_char_not_dvd3` — 3∤a（σ 単射で x̄₉³ ≠ 1 保存）。
   * `cr39_map_alpha`/`cr39_map_beta` — ι(x̄₃) = x̄₉³ = cm9Pow 3・ι(−1−x̄₃) = x̄₉⁶ = cm9Pow 6
     （x̄₉⁶ = −1−x̄₉³ は Φ_9(x̄₉) = 0 の帰結・cm9_nf_unique）。
   * `cr39Res`/`cr39Res_mem` — res 本体（id or cg3Conj）と Gal(ℚ(ζ₃)/ℚ) 所属。
   * `cr39_halpha`/`cr39_compat` — 意味論 ι∘res(σ) = σ∘ι（生成元 x̄₃ で確認 → 全点）。
   * `ce39Map_inj` — 埋め込み ι の単射性（0・3 次係数読み出し）。
   * `cr39_res_comp`/`cr39ResHom` — 群準同型 res(σ∘τ) = res(σ)∘res(τ)
     （compat + ι 単射 + cg3_aut_ext）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・2 段（ℚ(ζ₃) ⊂ ℚ(ζ₉)）のみの忠実な部分ケース。
   (ii)  **無限塔・逆極限 G_K は未達**（本ファイルは res₁ 単体＋compat＋群準同型まで。
         `ProfinitePi1Tower` への塔詰めは行わない——無限塔が本丸であり、定数延長で
         塔化するのは §3 規約の水増しに当たるため採らない）。
   (iii) **res の全射性は未証明**（M4 の σ_a 待ち）。分離性・正規性の一般論も未形式化。
   (iv)  K₁ = ℚ(ζ₃) は既存 cq3Field/qdfField(−3)/gfiCq3Field と同型な第 4 の担体
         （gefNF 表示）であり、同型による定理輸送は対象外。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicEmbed39
import IUT.CyclotomicMu9Roots
import IUT.CyclotomicGal3
import IUT.FundamentalGroup

namespace IUT

/-! ## CR39-0: σ の冪保存と rpow / cm9Pow の同一視 -/

/-- **CR39-0a: σ の冪保存** — 体自己同型 σ は冪を保つ:
    rpow(σ z) m = σ(rpow z m)。m 帰納（map_one で 0 次・map_mul で漸化）。 -/
theorem cr39_rpow_hom (σ : FieldAut p9iPhi9Field) (z : GefNF cpdPhi9 6) : ∀ m,
    rpow p9iPhi9Field.toCRing (σ.toFun z) m
      = σ.toFun (rpow p9iPhi9Field.toCRing z m) := by
  intro m
  induction m with
  | zero =>
    show p9iPhi9Field.toCRing.one = σ.toFun p9iPhi9Field.toCRing.one
    exact σ.map_one.symm
  | succ m ih =>
    show p9iPhi9Field.toCRing.mul (rpow p9iPhi9Field.toCRing (σ.toFun z) m) (σ.toFun z)
       = σ.toFun (p9iPhi9Field.toCRing.mul (rpow p9iPhi9Field.toCRing z m) z)
    rw [ih, σ.map_mul (rpow p9iPhi9Field.toCRing z m) z]

/-- **CR39-0b: rpow = cm9Pow** — ℚ(ζ₉) 上の rpow による x̄₉ の冪は gefNFPow による
    `cm9Pow`（環乗法の反復）と一致する（k 帰納・両者とも同じ NF 環の乗法）。 -/
theorem cr39_rpow_zeta (k : Nat) :
    rpow p9iPhi9Field.toCRing cm9Zeta k = cm9Pow k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show p9iPhi9Field.toCRing.mul (rpow p9iPhi9Field.toCRing cm9Zeta k) cm9Zeta
      = cm9Pow (k + 1)
    rw [ih]
    rfl

/-- **CR39-0c: σ(x̄₉)⁹ = 1** — map の 9 連鎖: σ(x̄₉)⁹ = σ(x̄₉⁹) = σ(1) = 1。
    冪保存 `cr39_rpow_hom` と `cm9_zeta_pow9`（x̄₉⁹ = 1）と `map_one`。 -/
theorem cr39_sigma_zeta9_pow9 (σ : FieldAut p9iPhi9Field) :
    rpow p9iPhi9Field.toCRing (σ.toFun cm9Zeta) 9 = p9iPhi9Field.toCRing.one := by
  rw [cr39_rpow_hom σ cm9Zeta 9, cr39_rpow_zeta 9, cm9_zeta_pow9]
  exact σ.map_one

/-! ## CR39-1: 指標 a = cm9Find(σ x̄₉) -/

/-- **CR39-1a: 指標 a** — σ(x̄₉) = x̄₉^a の a（構成的抽出 `cm9Find`）。 -/
def cr39Char (σ : FieldAut p9iPhi9Field) : Nat := cm9Find (σ.toFun cm9Zeta)

/-- **CR39-1b: a < 9**（`cm9Find_spec`・σ(x̄₉)⁹ = 1 の根性）。 -/
theorem cr39_char_lt (σ : FieldAut p9iPhi9Field) : cr39Char σ < 9 :=
  (cm9Find_spec (σ.toFun cm9Zeta) (cr39_sigma_zeta9_pow9 σ)).2

/-- **CR39-1c: σ(x̄₉) = x̄₉^a**（`cm9Find_spec`）。 -/
theorem cr39_char_spec (σ : FieldAut p9iPhi9Field) :
    σ.toFun cm9Zeta = cm9Pow (cr39Char σ) :=
  (cm9Find_spec (σ.toFun cm9Zeta) (cr39_sigma_zeta9_pow9 σ)).1

/-- **CR39-1d: σ(x̄₉^k) = x̄₉^{a·k}** — 冪保存 + 指標 + `cm9r_rpow_cm9Pow`。 -/
theorem cr39_sigma_pow (σ : FieldAut p9iPhi9Field) (k : Nat) :
    σ.toFun (cm9Pow k) = cm9Pow (cr39Char σ * k) := by
  rw [← cr39_rpow_zeta k, ← cr39_rpow_hom σ cm9Zeta k, cr39_char_spec σ]
  exact cm9r_rpow_cm9Pow (cr39Char σ) k

/-! ## CR39-2: 冪の周期性・σ の単射性・3∤a -/

/-- **CR39-2a: 冪の周期** — x̄₉^{9t+r} = x̄₉^r（x̄₉^{9t} = 1 で相殺）。 -/
theorem cm9_pow_period (t r : Nat) : cm9Pow (t * 9 + r) = cm9Pow r := by
  rw [cm9Pow_add (t * 9) r, cm9r_pow_mul9 t]
  exact cm9R.one_mul (cm9Pow r)

/-- **CR39-2b: σ は単射**（明示逆写像 `left_inv` の帰結）。 -/
theorem cr39_sigma_inj (σ : FieldAut p9iPhi9Field) {p q : GefNF cpdPhi9 6}
    (h : σ.toFun p = σ.toFun q) : p = q := by
  have hc : σ.invFun (σ.toFun p) = σ.invFun (σ.toFun q) := congrArg σ.invFun h
  rw [σ.left_inv p, σ.left_inv q] at hc
  exact hc

/-- **CR39-2c: 3∤a** — もし 3∣a なら σ(x̄₉³) = x̄₉^{3a} = x̄₉^{9t} = 1 = σ(1)、
    σ 単射で x̄₉³ = 1 となり `cm9_zeta_pow3_ne_one` に矛盾。 -/
theorem cr39_char_not_dvd3 (σ : FieldAut p9iPhi9Field) : ¬ 3 ∣ cr39Char σ := by
  intro hdvd
  obtain ⟨t, ht⟩ := hdvd
  have h1 : σ.toFun (cm9Pow 3) = cm9Pow (cr39Char σ * 3) := cr39_sigma_pow σ 3
  have h2 : cr39Char σ * 3 = t * 9 + 0 := by omega
  rw [h2, cm9_pow_period t 0] at h1
  have h4 : σ.toFun (cm9Pow 3) = σ.toFun cm9R.one := by
    rw [h1]; exact σ.map_one.symm
  have h5 : cm9Pow 3 = cm9R.one := cr39_sigma_inj σ h4
  exact cm9_zeta_pow3_ne_one h5

/-! ## CR39-3: ι(x̄₃) = x̄₉³ = cm9Pow 3 と ι(−1−x̄₃) = x̄₉⁶ = cm9Pow 6 -/

/-- **CR39-3a: ι(x̄₃) = x̄₉³** — 埋め込み ι は x̄₃ を x̄₉³ = cm9Pow 3 に送る
    （担体係数 (0,1) ↦ 3 次単項式・deg 3 < 6 で簡約不要）。 -/
theorem cr39_map_alpha : ce39Map cg3Alpha = cm9Pow 3 := by
  apply Subtype.ext
  funext j
  show ce39MapVal cg3Alpha j = (cm9Pow 3).val j
  rw [cm9_pow_small 3 (by omega)]
  show (if j = 0 then cg3Alpha.val 0 else if j = 3 then cg3Alpha.val 1 else ratRing.zero)
      = psSingle ratRing ratRing.one 3 j
  rw [cg3Alpha_val0, cg3Alpha_val1]
  cases Nat.decEq j 0 with
  | isTrue h =>
    rw [if_pos h, show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg (by omega)]
  | isFalse h0 =>
    rw [if_neg h0]
    cases Nat.decEq j 3 with
    | isTrue h3 =>
      rw [if_pos h3, show psSingle ratRing ratRing.one 3 j = ratRing.one from if_pos h3]
    | isFalse h3 =>
      rw [if_neg h3, show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg h3]

/-- **CR39-3b: x̄₉⁶ ≡ −1−x̄₉³ (mod Φ_9)** — Φ_9(x̄₉) = x̄₉⁶+x̄₉³+1 = 0 の直接帰結。
    X⁶ − (−1−X³) = X⁶+X³+1 = Φ_9 = 1·Φ_9 の合同（h = 1）。 -/
theorem cr39_x6_cong :
    gnfCong cpdPhi9 (psSingle ratRing ratRing.one 6) (ce39MapVal cg3Beta) := by
  refine ⟨psOne ratRing, ⟨1, fun j hj => if_neg (by omega)⟩, ?_⟩
  have hmul : ∀ j, psMul ratRing (psOne ratRing) cpdPhi9 j = cpdPhi9 j :=
    fun j => congrFun ((psRing ratRing).one_mul cpdPhi9) j
  funext j
  show ratRing.add (psSingle ratRing ratRing.one 6 j)
      (ratRing.neg (ce39MapVal cg3Beta j)) = psMul ratRing (psOne ratRing) cpdPhi9 j
  rw [hmul j, cm9_phi9_val j]
  show ratRing.add (psSingle ratRing ratRing.one 6 j)
      (ratRing.neg (if j = 0 then cg3Beta.val 0 else if j = 3 then cg3Beta.val 1
        else ratRing.zero))
    = (if j = 0 then ratRing.one else if j = 3 then ratRing.one
       else if j = 6 then ratRing.one else ratRing.zero)
  cases Nat.decEq j 0 with
  | isTrue h0 =>
    rw [if_pos h0, if_pos h0, cg3Beta_val0,
        show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg (by omega),
        CRing.neg_neg ratRing ratRing.one, ratRing.zero_add]
  | isFalse h0 =>
    rw [if_neg h0, if_neg h0]
    cases Nat.decEq j 3 with
    | isTrue h3 =>
      rw [if_pos h3, if_pos h3, cg3Beta_val1,
          show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg (by omega),
          CRing.neg_neg ratRing ratRing.one, ratRing.zero_add]
    | isFalse h3 =>
      rw [if_neg h3, if_neg h3]
      cases Nat.decEq j 6 with
      | isTrue h6 =>
        rw [if_pos h6, show psSingle ratRing ratRing.one 6 j = ratRing.one from if_pos h6,
            CRing.neg_zero ratRing, CRing.add_zero ratRing]
      | isFalse h6 =>
        rw [if_neg h6, show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg h6,
            CRing.neg_zero ratRing, CRing.add_zero ratRing]

/-- **CR39-3c: ι(−1−x̄₃) = x̄₉⁶** — β = −1−x̄₃ は ι で −1−x̄₉³ = x̄₉⁶ = cm9Pow 6 に。
    NF 一意性 `cm9_nf_unique`（x̄₉⁶ ≡ X⁶ ≡ −1−X³ = ι(β) の値）。 -/
theorem cr39_map_beta : ce39Map cg3Beta = cm9Pow 6 := by
  apply Subtype.ext
  have hu : (cm9Pow 6).val = ce39MapVal cg3Beta :=
    cm9_nf_unique (cm9Pow 6).val (ce39MapVal cg3Beta) (cm9Pow 6).property
      (ce39MapVal_bnd cg3Beta)
      (gnfCong_trans cpdPhi9 (cm9_pow_cong 6) cr39_x6_cong)
  exact hu.symm

/-! ## CR39-4: res 本体と Gal(ℚ(ζ₃)/ℚ) 所属 -/

/-- **CR39-4a: 制限準同型 res(σ)** — a = cr39Char σ に対し a mod 3 = 1 なら恒等、
    さもなくば共役 cg3Conj。K₁ 側は cg3 で自己同型 2 個と完全決定済みなので、
    K₁ 側の代入準同型を再構成せずに res を定める。 -/
def cr39Res (σ : FieldAut p9iPhi9Field) : FieldAut cnfPhi3Field :=
  if cr39Char σ % 3 = 1 then fieldAutId cnfPhi3Field else cg3Conj

/-- **CR39-4b: res(σ) ∈ Gal(ℚ(ζ₃)/ℚ)** — id も cg3Conj も ℚ 各点固定。 -/
theorem cr39Res_mem (σ : FieldAut p9iPhi9Field) :
    (galoisSubgroup cnfExt3).mem (cr39Res σ) := by
  show (galoisSubgroup cnfExt3).mem
      (if cr39Char σ % 3 = 1 then fieldAutId cnfPhi3Field else cg3Conj)
  cases Nat.decEq (cr39Char σ % 3) 1 with
  | isTrue h => rw [if_pos h]; exact (galoisSubgroup cnfExt3).one_mem
  | isFalse h => rw [if_neg h]; exact cg3Conj_mem

/-! ## CR39-5: 生成元での意味論 halpha と全点 compat -/

/-- **CR39-5a: 生成元での意味論** — ι(res(σ)(x̄₃)) = σ(ι(x̄₃))。
    σ(ι(x̄₃)) = σ(x̄₉³) = x̄₉^{3a}。3a mod 9 ∈ {3,6} の 2 分岐:
    a≡1 ⟹ res(σ)=id・ι(x̄₃) = x̄₉³ = x̄₉^{3a}、
    a≢1（3∤a ⟹ a≡2）⟹ res(σ)=cg3Conj・ι(−1−x̄₃) = x̄₉⁶ = x̄₉^{3a}。 -/
theorem cr39_halpha (σ : FieldAut p9iPhi9Field) :
    ce39Map ((cr39Res σ).toFun cg3Alpha) = σ.toFun (ce39Map cg3Alpha) := by
  rw [cr39_map_alpha, cr39_sigma_pow σ 3]
  cases Nat.decEq (cr39Char σ % 3) 1 with
  | isTrue h =>
    have hres : (cr39Res σ).toFun cg3Alpha = cg3Alpha := by
      show (if cr39Char σ % 3 = 1 then fieldAutId cnfPhi3Field else cg3Conj).toFun cg3Alpha
        = cg3Alpha
      rw [if_pos h]
      rfl
    rw [hres, cr39_map_alpha]
    have ha3 : cr39Char σ * 3 = (cr39Char σ / 3) * 9 + 3 := by omega
    rw [ha3, cm9_pow_period (cr39Char σ / 3) 3]
  | isFalse h =>
    have hnd : ¬ 3 ∣ cr39Char σ := cr39_char_not_dvd3 σ
    have hres : (cr39Res σ).toFun cg3Alpha = cg3Beta := by
      show (if cr39Char σ % 3 = 1 then fieldAutId cnfPhi3Field else cg3Conj).toFun cg3Alpha
        = cg3Beta
      rw [if_neg h]
      show cg3ConjFun cg3Alpha = cg3Beta
      exact cg3_conj_alpha
    rw [hres, cr39_map_beta]
    have ha3 : cr39Char σ * 3 = (cr39Char σ / 3) * 9 + 6 := by omega
    rw [ha3, cm9_pow_period (cr39Char σ / 3) 6]

/-- **CR39-5b: 意味論 compat（本丸）** — ι ∘ res(σ) = σ ∘ ι（全点）。任意の x を
    x = ι₃(x₀) + ι₃(x₁)·x̄₃ に分解し（`cg3_decompose`）、環準同型性（res(σ)・ι・σ）
    と ℚ の固定（res(σ)_mem・hσ）と incl 適合（`ce39_incl_compat`）で
    生成元 x̄₃ の一致（`cr39_halpha`）に帰着させる。 -/
theorem cr39_compat (σ : FieldAut p9iPhi9Field)
    (hσ : (galoisSubgroup p9iExt9).mem σ) :
    ∀ x, ce39Map ((cr39Res σ).toFun x) = σ.toFun (ce39Map x) := by
  intro x
  rw [cg3_decompose x,
      (cr39Res σ).map_add, (cr39Res σ).map_mul,
      cr39Res_mem σ (x.val 0), cr39Res_mem σ (x.val 1),
      ce39_map_add, ce39_map_mul, ce39_incl_compat, ce39_incl_compat,
      ce39_map_add, ce39_map_mul, ce39_incl_compat, ce39_incl_compat,
      σ.map_add, σ.map_mul, hσ (x.val 0), hσ (x.val 1), cr39_halpha σ]

/-! ## CR39-6: ι の単射性 -/

/-- **CR39-6: 埋め込み ι は単射** — 担体係数 0・3 次（= x̄₃ の 0・1 次）の読み出し。 -/
theorem ce39Map_inj (u v : GefNF cq0PS 2) (h : ce39Map u = ce39Map v) : u = v := by
  have hval : ce39MapVal u = ce39MapVal v := congrArg Subtype.val h
  have h0 : u.val 0 = v.val 0 := by
    have hj := congrFun hval 0
    rw [show ce39MapVal u 0 = u.val 0 from if_pos rfl,
        show ce39MapVal v 0 = v.val 0 from if_pos rfl] at hj
    exact hj
  have h1 : u.val 1 = v.val 1 := by
    have hj := congrFun hval 3
    rw [show ce39MapVal u 3 = u.val 1 from (if_neg (by omega)).trans (if_pos rfl),
        show ce39MapVal v 3 = v.val 1 from (if_neg (by omega)).trans (if_pos rfl)] at hj
    exact hj
  exact cg3_carrier_ext u v h0 h1

/-! ## CR39-7: 群準同型性 res(σ∘τ) = res(σ)∘res(τ) -/

/-- **CR39-7a: res は乗法的** — res(σ∘τ) = res(σ)∘res(τ)。両辺は Gal(ℚ(ζ₃)/ℚ) の
    元で、生成元 x̄₃ での一致（`cg3_aut_ext`）に帰着。ι の単射性で
    ι(res(σ∘τ) x̄₃) = ι(res(σ)(res(τ) x̄₃)) を compat の 3 連鎖
    ι∘res = ∘σ (× 2) で σ(τ(ι x̄₃)) に揃える。 -/
theorem cr39_res_comp (σ τ : FieldAut p9iPhi9Field)
    (hσ : (galoisSubgroup p9iExt9).mem σ) (hτ : (galoisSubgroup p9iExt9).mem τ) :
    cr39Res (fieldAutComp σ τ) = fieldAutComp (cr39Res σ) (cr39Res τ) := by
  refine cg3_aut_ext (cr39Res (fieldAutComp σ τ)) (fieldAutComp (cr39Res σ) (cr39Res τ))
    (cr39Res_mem (fieldAutComp σ τ))
    ((galoisSubgroup cnfExt3).mul_mem (cr39Res_mem σ) (cr39Res_mem τ)) ?_
  apply ce39Map_inj
  have hAeq : ce39Map ((cr39Res (fieldAutComp σ τ)).toFun cg3Alpha)
      = σ.toFun (τ.toFun (ce39Map cg3Alpha)) :=
    cr39_compat (fieldAutComp σ τ) ((galoisSubgroup p9iExt9).mul_mem hσ hτ) cg3Alpha
  have hBeq : ce39Map ((fieldAutComp (cr39Res σ) (cr39Res τ)).toFun cg3Alpha)
      = σ.toFun (τ.toFun (ce39Map cg3Alpha)) := by
    show ce39Map ((cr39Res σ).toFun ((cr39Res τ).toFun cg3Alpha))
        = σ.toFun (τ.toFun (ce39Map cg3Alpha))
    rw [cr39_compat σ hσ ((cr39Res τ).toFun cg3Alpha), cr39_compat τ hτ cg3Alpha]
  rw [hAeq, hBeq]

/-- **CR39-7b: 制限準同型 res : Gal(ℚ(ζ₉)/ℚ) → Gal(ℚ(ζ₃)/ℚ)** — 群準同型（`Hom`）。
    map は res 本体、map_mul は `cr39_res_comp`。`ProfinitePi1Tower.restr` witness の
    初の本物 discharge の核（塔詰めは無限塔が本丸のため本ファイルでは行わない）。 -/
def cr39ResHom : Hom (galoisGroupGrp p9iExt9) (galoisGroupGrp cnfExt3) where
  map := fun a => ⟨cr39Res a.val, cr39Res_mem a.val⟩
  map_mul := fun a b => by
    apply Subtype.ext
    show cr39Res (fieldAutComp a.val b.val)
        = fieldAutComp (cr39Res a.val) (cr39Res b.val)
    exact cr39_res_comp a.val b.val a.property b.property

end IUT
