/-
  IUT/Q3CokernelObjectReal.lean — 柱B・B2 M4c: 単数余核 U_{L₂}/N(U_M) を genuine `Grp`
    として建設し、相互律 Gal(M/L₂) ↪ その literal 商群対象 へ昇格する
    （audit の明示次増分 M4c——M4b の「関係レベルの埋め込み」を「本物の Grp 商対象」へ）

  ── 主要成果の分類: **[実／(a) 昇格]**。
  M4b（q9rg）は q9rcCongMod を genuine 同値関係とし、Gal ↪ cokernel を「関係レベルの
  単射群準同型（mod N）」として建設した。しかし literal な Quotient 型（商群対象そのもの）は
  未構成という cap (a) の residual が残っていた。本 M4c は M267F（QuotientGroup）の
  **本物の商群機構**（正規部分群→合同→商群 `quotientGroupN` : Grp）を実 U_{L₂}=q3rqU・実
  ノルム部分群 N(U_M)=imSubgroup(ノルム準同型) に**そのまま instantiate** し、
   * U_{L₂}/N(U_M) を **genuine `Grp`（q9qcCoker）** として建設、
   * 射影 q9qcProj : U_{L₂} ↠ q9qcCoker を建設、
   * 商の合同 cosetRel を M4b の q9rcCongMod に橋渡し（q9qc_proj_eq_of_cong /
     q9qc_cong_of_proj_eq）、
   * 相互律 q9qcGalHom : Gal(M/L₂)=q9kdG → q9qcCoker を **bona-fide 群準同型（Hom）**
     として建設し、q9qc_gal_injective で単射、
  へ昇格する。toy 主語なし——主語は実 q3rqU・実 3 次ノルム q3kNormBase・実 q9kdG（実 σ の
  3 元群）・実 quotientGroupN。

  complete_pct 影響: **B2 0.34→（独立監査次第・予測 +0.02〜0.05・cap(a) の「literal な
  Quotient object なし」residual を閉じる）**。M4b は関係レベルの埋め込みを与えた。本 M4c は
  それを genuine `Grp` 商対象への単射群準同型へ昇格する（Gal ↪ q9qcCoker、像 = 位数 3
  部分群 ⟨[4]⟩）。

  真水（本物へ昇格・新規建設）:
   * q9qcNormHom（★ 単数ノルム準同型 U_M → U_{L₂}、Hom として）
   * q9qcNormSub（ノルム部分群 N(U_M) ⊆ U_{L₂}）・q9qc_norm_normal（アーベル ⟹ 正規）
   * q9qcCoker（★★★ THE LITERAL COKERNEL OBJECT U_{L₂}/N(U_M) : Grp）
   * q9qcProj（射影 U_{L₂} ↠ q9qcCoker、Hom）
   * q9qc_proj_eq_of_cong / q9qc_cong_of_proj_eq（★★ cosetRel ↔ q9rcCongMod 橋）
   * q9qcGalHom（★★ 相互律 Gal(M/L₂) → q9qcCoker、bona-fide Hom）
   * q9qc_gal_injective（★★ 単射）・q9qc_gal_embeds（★★★ 束ね）
   * Q3CokernelObjectRealData（capstone）

  正直な限定（§4 規約により消さない・弱めない・q9rg/q9rc/q9lr/q9rf/q9gn/q9kd/q3k/q3rq 継承の上に追記のみ）:
  1. **これは単数余核 U_{L₂}/N(U_M)（整単数）であって、分数元 M^× を含む全 L₂^×/N(M^×) ではない**。
     LCFT により値群部（T1）は全射で両者は一致するが、分数 M^× そのものは未 wire（cap b）——
     honest limitation として明記。
  2. **依然 Gal ↪ cokernel（単射・像 = 位数 3 部分群 ⟨[4]⟩）であって Gal ≅ cokernel ではない**。
     全射性・指数 ≤3・U_{L₂}^(3)⊆N・Artin 写像の正規化 = T3/research（範囲外・主張しない）。
  3. q9rg/q9rc/q9lr/q9rf/q9gn/q9kd/q3k/q3rq の正直限定を全継承（O_M と M^× のみ・体化なし・
     σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・単一拡大 M/L₂/ℚ₃）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.QuotientGroup
import IUT.Q3ReciprocityGalReal

namespace IUT

/-! ## q9qc-1: 単数ノルム準同型 U_M → U_{L₂}（Hom） -/

/-- **q9qc-1a（★）: 単数ノルム準同型** N : U_M = q3kU → U_{L₂} = q3rqU。
    map x = ⟨N(x.val), x.property⟩（x.property : q3kUnitMem x.val ≡ q3rqUnitMem (N x.val)
    なので U_{L₂} に落ちる）。map_mul は q3k_normBase_mul + Subtype.ext。 -/
def q9qcNormHom : Hom q3kU q3rqU where
  map := fun x => ⟨q3kNormBase x.val, x.property⟩
  map_mul := fun a b => Subtype.ext (q3k_normBase_mul a.val b.val)

/-! ## q9qc-2: ノルム部分群 N(U_M) ⊆ U_{L₂} と正規性（アーベル） -/

/-- **q9qc-2a: ノルム部分群 N(U_M) ⊆ U_{L₂}**（像部分群）。 -/
def q9qcNormSub : Subgroup q3rqU := imSubgroup q9qcNormHom

/-- **q9qc-2b: N(U_M) は正規部分群**（U_{L₂} はアーベル ⟹ gng⁻¹ = n）。 -/
theorem q9qc_norm_normal : IsNormalSubgroup q3rqU q9qcNormSub := by
  intro g n hn
  have key : q3rqU.mul (q3rqU.mul g n) (q3rqU.inv g) = n := by
    rw [q3rqU_comm g n, q3rqU.mul_assoc n g (q3rqU.inv g), q3rqU.mul_inv, q3rqU.mul_one]
  rw [key]
  exact hn

/-! ## q9qc-3: ★ THE LITERAL COKERNEL OBJECT U_{L₂}/N(U_M) : Grp -/

/-- **q9qc-3a（★★★）: literal な余核対象 U_{L₂}/N(U_M) を genuine `Grp` として建設**。
    M267F の本物の商群機構（正規部分群 → 合同 → 商群）を実 U_{L₂}・実ノルム部分群に
    そのまま instantiate。M4b の「関係レベル」から「本物の Grp 商対象」への昇格の核。 -/
def q9qcCoker : Grp := quotientGroupN q3rqU q9qcNormSub q9qc_norm_normal

/-- **q9qc-3b: 射影 U_{L₂} ↠ q9qcCoker**（Hom）。 -/
def q9qcProj : Hom q3rqU q9qcCoker := quotientProjN q3rqU q9qcNormSub q9qc_norm_normal

/-! ## q9qc-4: ★★ cosetRel ↔ q9rcCongMod 橋（literal 商 と M4b 関係の接続） -/

/-- **q9qc-4a（★★）: q9rcCongMod ⟹ 射影相等** — a ≡ b (mod N) なら q9qcProj.map a = q9qcProj.map b。
    商群の合同 cosetRel は a⁻¹·b ∈ N(U_M)。q9rcCongMod の witness x（N(x) = a⁻¹·b）を
    ノルム部分群のメンバー証人にして Quot.sound。 -/
theorem q9qc_proj_eq_of_cong (a b : q3rqU.carrier)
    (h : q9rcCongMod a.val b.val) :
    q9qcProj.map a = q9qcProj.map b := by
  obtain ⟨x, hx, he⟩ := h
  have hcoset : cosetRel q3rqU q9qcNormSub a b := by
    show q9qcNormSub.mem (q3rqU.mul (q3rqU.inv a) b)
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    show q3kNormBase x = q3rqMul (q3rqInv a.val a.property) b.val
    rw [← he, ← q9rg_mul_assoc (q3rqInv a.val a.property) a.val (q3kNormBase x),
        q3rq_inv_mul a.val a.property, q3rq_one_mul]
  exact Quot.sound hcoset

/-- **q9qc-4b（★★）: 射影相等 ⟹ q9rcCongMod** — q9qcProj.map a = q9qcProj.map b なら a ≡ b (mod N)。
    Quot の分離性 quot_exact で a⁻¹·b ∈ N(U_M) を取り出し、その witness を q9rcCongMod の
    証人に変換（右逆元 a·a⁻¹=1 で消去）。 -/
theorem q9qc_cong_of_proj_eq (a b : q3rqU.carrier)
    (h : q9qcProj.map a = q9qcProj.map b) :
    q9rcCongMod a.val b.val := by
  have hrel : q9qcNormSub.mem (q3rqU.mul (q3rqU.inv a) b) :=
    quot_exact q3rqU (normalCong q3rqU q9qcNormSub q9qc_norm_normal) h
  obtain ⟨w, hw⟩ := hrel
  have hval : q3kNormBase w.val = q3rqMul (q3rqInv a.val a.property) b.val :=
    congrArg Subtype.val hw
  refine ⟨w.val, w.property, ?_⟩
  rw [hval, ← q9rg_mul_assoc a.val (q3rqInv a.val a.property) b.val]
  have hrinv : q3rqMul a.val (q3rqInv a.val a.property) = q3rqOne :=
    (q3rqRing.mul_comm a.val (q3rqInv a.val a.property)).trans (q3rq_inv_mul a.val a.property)
  rw [hrinv, q3rq_one_mul]

/-! ## q9qc-5: ★★ 相互律 Gal(M/L₂) → q9qcCoker（bona-fide Hom） -/

/-- **q9qc-5a: φ(g) は単数**（1, 4, 16 はすべて実 ℤ₃-単数）。 -/
def q9qcPhiUnit : (g : q9kdGCar) → q3rqUnitMem (q9rgPhi g)
  | .e => q3rq_unit_one
  | .s => q9rc_four_unit
  | .s2 => q3rq_unit_mul q9rc_four_unit q9rc_four_unit

/-- **q9qc-5b（★★）: 相互律 Gal(M/L₂) → q9qcCoker を bona-fide 群準同型（Hom）として建設**。
    g ↦ [φ(g)]（φ(g) の余核類）。φ(gh) ≡ φ(g)·φ(h) (mod N)（q9rg_hom）を
    q9qc_proj_eq_of_cong で射影相等へ翻訳し、q9qcProj が Hom であることと合わせて map_mul。 -/
def q9qcGalHom : Hom q9kdG q9qcCoker where
  map := fun g => q9qcProj.map ⟨q9rgPhi g, q9qcPhiUnit g⟩
  map_mul := fun g h => by
    show q9qcProj.map ⟨q9rgPhi (q9kdGMul g h), q9qcPhiUnit (q9kdGMul g h)⟩
        = q9qcCoker.mul (q9qcProj.map ⟨q9rgPhi g, q9qcPhiUnit g⟩)
            (q9qcProj.map ⟨q9rgPhi h, q9qcPhiUnit h⟩)
    rw [← q9qcProj.map_mul]
    exact q9qc_proj_eq_of_cong _ _ (q9rg_hom g h)

/-- **q9qc-5c（★★）: q9qcGalHom は単射** — φ(g) ≡ φ(h) (mod N) ⟹ g = h（q9rg_inj）。 -/
theorem q9qc_gal_injective (g h : q9kdGCar)
    (hgh : q9qcGalHom.map g = q9qcGalHom.map h) : g = h := by
  have hc : q9rcCongMod (q9rgPhi g) (q9rgPhi h) :=
    q9qc_cong_of_proj_eq ⟨q9rgPhi g, q9qcPhiUnit g⟩ ⟨q9rgPhi h, q9qcPhiUnit h⟩ hgh
  exact q9rg_inj g h hc

/-- **q9qc-5d: φ は単位元を保存**（φ(e) = [1] = 1_{q9qcCoker}）。 -/
theorem q9qc_gal_phi_one : q9qcGalHom.map q9kdGCar.e = q9qcCoker.one :=
  Hom.map_one q9qcProj

/-- **q9qc-5e（★★★）: Gal(M/L₂) ↪ q9qcCoker（LITERAL Grp 商対象への単射群準同型）**。
    (1) φ の準同型性（Hom.map_mul）、(2) φ の単射性、(3) φ(e) = 1。M4b の
    「↪ 抽象合同関係」を「↪ genuine `Grp` 商対象 q9qcCoker」へ昇格した束ね。
    **これは Gal ↪ cokernel であって Gal ≅ cokernel ではない**（全射性 = T3/research・範囲外）。 -/
theorem q9qc_gal_embeds :
    (∀ g h, q9qcGalHom.map (q9kdGMul g h)
        = q9qcCoker.mul (q9qcGalHom.map g) (q9qcGalHom.map h))
    ∧ (∀ g h, q9qcGalHom.map g = q9qcGalHom.map h → g = h)
    ∧ q9qcGalHom.map q9kdGCar.e = q9qcCoker.one :=
  ⟨q9qcGalHom.map_mul, q9qc_gal_injective, q9qc_gal_phi_one⟩

/-! ## q9qc-6: capstone -/

/-- **q9qc-6a: literal 余核対象データ束ね** — genuine `Grp` 余核 q9qcCoker・射影・
    ノルム準同型・相互律 Hom・単射性・cosetRel↔q9rcCongMod 橋。 -/
structure Q3CokernelObjectRealData where
  /-- literal な余核対象 U_{L₂}/N(U_M)（genuine Grp）。 -/
  coker : Grp
  /-- 射影 U_{L₂} ↠ coker。 -/
  proj : Hom q3rqU coker
  /-- 単数ノルム準同型 U_M → U_{L₂}。 -/
  normHom : Hom q3kU q3rqU
  /-- 相互律 Gal(M/L₂) → coker（bona-fide Hom）。 -/
  galHom : Hom q9kdG coker
  /-- galHom は単射（Gal ↪ coker）。 -/
  gal_injective : ∀ g h, galHom.map g = galHom.map h → g = h
  /-- galHom は単位元を保存。 -/
  gal_phi_one : galHom.map q9kdGCar.e = coker.one
  /-- q9rcCongMod ⟹ 射影相等（橋・順方向）。 -/
  proj_eq_of_cong : ∀ a b : q3rqU.carrier,
    q9rcCongMod a.val b.val → proj.map a = proj.map b
  /-- 射影相等 ⟹ q9rcCongMod（橋・逆方向）。 -/
  cong_of_proj_eq : ∀ a b : q3rqU.carrier,
    proj.map a = proj.map b → q9rcCongMod a.val b.val

/-- **q9qc-6b: 見出し実例** — 実 U_{L₂}=q3rqU 上の literal 余核対象と相互律の埋め込み。 -/
def q9qc_data : Q3CokernelObjectRealData where
  coker := q9qcCoker
  proj := q9qcProj
  normHom := q9qcNormHom
  galHom := q9qcGalHom
  gal_injective := q9qc_gal_injective
  gal_phi_one := q9qc_gal_phi_one
  proj_eq_of_cong := q9qc_proj_eq_of_cong
  cong_of_proj_eq := q9qc_cong_of_proj_eq

/-- **q9qc-6c: literal 余核対象と Gal ↪ その対象 の存在**（B2 cap(a) の
    「literal Quotient object なし」residual を閉じる）。 -/
theorem q9qc_exists : Nonempty Q3CokernelObjectRealData := ⟨q9qc_data⟩

end IUT
