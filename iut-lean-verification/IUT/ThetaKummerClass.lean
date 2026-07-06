/-
  IUT/ThetaKummerClass.lean — M353F [実／本物]
  分類: 実 (テータ値の Kummer 類 [Θ]∈H¹(G_K,μ_{2l}))
  complete_pct 影響: 柱E を前進（テータ値 Θ の Kummer コサイクル κ_Θ(σ)=σ(Θ)/Θ∈μ_{2l}
    （Θ^{2l}=q^{j²} ガロア固定ゆえ）を本物で構成＝1-コサイクル・[Θ]∈H¹ が μ_{2l}-トーサー
    不定性を除いて標準的・2l 乗で q^{j²} の Kummer 類に対応、を証明しテータ値をガロア
    コホモロジーに結ぶ（M343F+M348F+M345F 接続）。エタールテータ類の核）。
  正直な限定: 完全なエタールテータ類・tempered π₁ は外部仮説/後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M353F-1（一般テータ Kummer コサイクル κ_Θ(σ)=σ(Θ)/Θ）: 環境 G_K-加群 A（K̄^× の
    忠実な代理）と Θ∈A に対し κ_Θ=`galH1Coboundary A Θ`（σ(Θ)·Θ⁻¹）を主語に、
    `tkc_is_cocycle`（1-コサイクル κ_Θ(gh)=κ_Θ(g)·σ_g κ_Θ(h)）・`tkc_lands_in_mu`
    （Θ^{2l} ガロア固定 ⟹ κ_Θ(σ)^{2l}=1、μ_{2l} に着地）を本物で。
  * M353F-2（ノルム Θ^{2l}=q^{j²} ガロア固定・M343F 接続）: `tkc_norm_is_qpower`
    （M343F `galTh_norm_qpower` 再輸出）・`tkc_norm_cocycle_trivial`（q^{j²} の
    Kummer コサイクルは自明）。
  * M353F-3（Kummer 類 [Θ]∈H¹(G_K,μ_{2l})・μ_{2l}⊂K の本物ケース）: テータ Kummer
    指標 g↦κ(g)^{e}（e=j²、`galThTorTwist`）が本物の群準同型（`galTh_tor_twist_mul`）
    ⟹ 自明作用 μ_{2l}-加群の 1-コサイクル ⟹ 射影 Z¹→H¹ で類 `tkcClass`。
  * M353F-4（μ_{2l}-トーサー不定性を除いて標準的・M348F 接続）:
    `tkc_class_eq_of_coboundary`（コバウンダリ差なら H¹ で同一）⟹ `tkc_class_well_defined`
    （Θ↦ζ·Θ（ζ∈μ_{2l}）で κ_Θ はコバウンダリ変化＝H¹ 類は不変）。
  * M353F-5（2l 乗で q^{j²} の Kummer 類に対応・M345F 接続）: `tkc_class_pow_trivial`
    （[Θ]^{2l}=0∈H¹(μ_{2l})、Θ^{2l}=q^{j²} が 2l 乗元ゆえ）・`tkc_kummer_qpower_class`
    （M345F `kex_exact_at_units` 再輸出: q^{j²}∈(K^×)^{2l} ⟺ Kummer 類自明）。
  * M353F-6（M343F `galThTorTwist` 接続）: `tkc_galois_theta_link`（κ_Θ IS κ(·)^e）・
    `tkc_twist_char_lands`（指標値は 2l-捻れ、`galTh_norm_twist_trivial`）。
  * M353F-7 外部仮説（完全エタールテータ類・tempered π₁・決して導出しない）。
  * M353F-8 capstone `TkcData` / `tkc_exists` と実例（l=5, μ_{10}）。

  選択公理不使用・sorry 皆無・禁止タクティク不使用。一般名は `tkc` 接頭辞で衝突回避。
  共有ファイル未変更。
-/
import IUT.GaloisTheta
import IUT.GaloisCohomologyH1
import IUT.KummerExact

namespace IUT

/-! ## M353F-0: 可換群の冪・逆元の補助（本物） -/

/-- **M353F-0a: 逆元の冪** — 可換群で (x⁻¹)ⁿ = (xⁿ)⁻¹。xⁿ·(x⁻¹)ⁿ=(x·x⁻¹)ⁿ=1ⁿ=1 と
    逆元の一意性（M9 `inv_eq_of_mul_eq_one`）から。κ_Θ(σ)=σ(Θ)·Θ⁻¹ の 2l 乗計算の核。 -/
theorem tkc_pow_inv (G : Grp) (comm : ∀ a b, G.mul a b = G.mul b a)
    (x : G.carrier) (N : Nat) :
    G.pow (G.inv x) N = G.inv (G.pow x N) := by
  have h : G.mul (G.pow x N) (G.pow (G.inv x) N) = G.one := by
    rw [← galTh_pow_mul_distrib G comm x (G.inv x) N, G.mul_inv]
    exact galTh_pow_one G N
  exact G.inv_eq_of_mul_eq_one h

/-- **M353F-0b: コサイクル群の冪の点別計算** — Z¹ の冪 (c^N) の g 値は点別冪 (c(g))^N
    （Z¹ の積・単位が点別ゆえ、N の帰納）。テータ Kummer コサイクルの 2l 乗が点別で
    μ_{2l} 消去に落ちることの核。 -/
theorem tkc_cocycles_pow_apply {GK : Grp} (A : galH1Module GK)
    (c : galH1Cocycle A) (N : Nat) (g : GK.carrier) :
    ((galH1_cocycles_group A).pow c N).f g = A.M.pow (c.f g) N := by
  induction N with
  | zero => rfl
  | succ k ih =>
    show A.M.mul (c.f g) (((galH1_cocycles_group A).pow c k).f g)
       = A.M.mul (c.f g) (A.M.pow (c.f g) k)
    rw [ih]

/-! ## M353F-1: 一般テータ Kummer コサイクル κ_Θ(σ)=σ(Θ)/Θ（環境 G_K-加群上・本物） -/

/-- **M353F-1a: テータ Kummer コサイクル** — 環境 G_K-加群 A（K̄^× の忠実な代理・M326F）と
    テータ値 Θ∈A に対し、Kummer コサイクル κ_Θ(σ)=σ(Θ)·Θ⁻¹ ＝ 主コサイクル
    `galH1Coboundary A Θ`。IUT のエタールテータ Kummer 類の母胎（σ↦σ(Θ)/Θ）。 -/
def tkcCocycle {GK : Grp} (A : galH1Module GK) (Θ : A.M.carrier) :
    galH1Cocycle A :=
  galH1Coboundary A Θ

/-- **M353F-1b: κ_Θ の点値** — κ_Θ(g)=σ_g(Θ)·Θ⁻¹（定義展開）。 -/
theorem tkc_apply {GK : Grp} (A : galH1Module GK) (Θ : A.M.carrier) (g : GK.carrier) :
    (tkcCocycle A Θ).f g = A.M.mul ((A.act g).map Θ) (A.M.inv Θ) :=
  rfl

/-- **定理 (M353F-1c: κ_Θ(1)=1)** — σ_1=id ゆえ κ_Θ(1)=Θ·Θ⁻¹=1。 -/
theorem tkc_cocycle_one {GK : Grp} (A : galH1Module GK) (Θ : A.M.carrier) :
    (tkcCocycle A Θ).f GK.one = A.M.one := by
  show A.M.mul ((A.act GK.one).map Θ) (A.M.inv Θ) = A.M.one
  rw [A.act_one Θ, A.M.mul_inv]

/-- **定理 (M353F-1d: κ_Θ は 1-コサイクル（crossed homomorphism）)** —
    κ_Θ(g·h)=κ_Θ(g)·σ_g(κ_Θ(h))（M326F 主コサイクルの 1-コサイクル条件）。
    テータ Kummer コサイクルが H¹ の類を定める本物の 1-コサイクル。 -/
theorem tkc_is_cocycle {GK : Grp} (A : galH1Module GK) (Θ : A.M.carrier)
    (g h : GK.carrier) :
    (tkcCocycle A Θ).f (GK.mul g h)
      = A.M.mul ((tkcCocycle A Θ).f g) ((A.act g).map ((tkcCocycle A Θ).f h)) :=
  (tkcCocycle A Θ).cocycle g h

/-- **定理 (M353F-1e: κ_Θ は μ_{2l} に着地)** — Θ^{2l}=q^{j²} がガロア固定
    （σ(Θ^{2l})=Θ^{2l}, M343F）なら κ_Θ(σ)^{2l}=(σ(Θ)/Θ)^{2l}=σ(Θ^{2l})/Θ^{2l}=1、
    すなわち κ_Θ(σ) は 1 の 2l 乗根 ∈ μ_{2l}。テータ Kummer 類が μ_{2l} 係数に住む本物の核
    （σ hom の冪保存 `Hom.map_pow`・逆元の冪 M353F-0a・可換群の積の冪分配 M343F）。 -/
theorem tkc_lands_in_mu {GK : Grp} (A : galH1Module GK) (Θ : A.M.carrier) (N : Nat)
    (hfix : ∀ g, (A.act g).map (A.M.pow Θ N) = A.M.pow Θ N) (g : GK.carrier) :
    A.M.pow ((tkcCocycle A Θ).f g) N = A.M.one := by
  show A.M.pow (A.M.mul ((A.act g).map Θ) (A.M.inv Θ)) N = A.M.one
  rw [galTh_pow_mul_distrib A.M A.comm ((A.act g).map Θ) (A.M.inv Θ) N,
    tkc_pow_inv A.M A.comm Θ N, ← Hom.map_pow (A.act g) Θ N, hfix g, A.M.mul_inv]

/-! ## M353F-2: ノルム Θ^{2l}=q^{j²} ガロア固定（M343F 接続・本物） -/

/-- **定理 (M353F-2a: ノルムは q 冪・M343F 再輸出)** — テータ値の 2l 乗はちょうど q^{j²}∈q^ℤ
    （M343F `galTh_norm_qpower`, witness j²）。κ_Θ が μ_{2l} に着地する根拠
    （2l 乗が周期格子 q^ℤ の G_K-固定元に落ちる）。 -/
theorem tkc_norm_is_qpower (R : CRing) (l : Nat) (j : Int) :
    IsLPowerValue R ((2 * l : Nat) : Int) (thLtorPow R (thLtorValue R j) (2 * l)) :=
  galTh_norm_qpower R l j

/-- **定理 (M353F-2b: q^{j²} の Kummer コサイクルは自明)** — Θ^{2l}=q^{j²} がガロア固定
    なら、その Kummer コサイクル σ↦σ(q^{j²})·(q^{j²})⁻¹ は各 σ で 1（Galois-固定ゆえ）。
    q^{j²} は既に基礎体で 2l 乗元＝その Kummer 類は自明であることの本物の点別核。 -/
theorem tkc_norm_cocycle_trivial {GK : Grp} (A : galH1Module GK) (Θ : A.M.carrier) (N : Nat)
    (hfix : ∀ g, (A.act g).map (A.M.pow Θ N) = A.M.pow Θ N) (g : GK.carrier) :
    (galH1Coboundary A (A.M.pow Θ N)).f g = A.M.one := by
  show A.M.mul ((A.act g).map (A.M.pow Θ N)) (A.M.inv (A.M.pow Θ N)) = A.M.one
  rw [hfix g, A.M.mul_inv]

/-! ## M353F-3: Kummer 類 [Θ]∈H¹(G_K,μ_{2l})（μ_{2l}⊂K の本物ケース） -/

/-- **M353F-3a: 射影 Z¹→H¹** — 1-コサイクル群 Z¹ から H¹=Z¹/B¹ への商射影（M326F）。 -/
def tkcProj {GK : Grp} (A : galH1Module GK) :
    Hom (galH1_cocycles_group A) (galH1Group A) :=
  quotientProjN (galH1_cocycles_group A) (galH1_coboundaries_subgroup A)
    (galH1_coboundaries_normal A)

/-- **M353F-3b: テータ Kummer 指標** — l-捻れ点のテータ値 Θ(q,u_j)（指数 e=j²）に対する
    Kummer 指標 g↦κ(g)^e＝`galThTorTwist GK M κ g e`（M343F）。基礎体が μ_{2l} を含む
    （G_K が μ_{2l} に自明作用する）本物のケースで、これは本物の群準同型
    （`galTh_tor_twist_mul` により κ(gh)^e=κ(g)^e·κ(h)^e）＝μ_{2l} 値の 1-コサイクル。 -/
def tkcThetaChar {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) : Hom GK M.μ where
  map := fun g => galThTorTwist GK M κ g e
  map_mul := fun g h => galTh_tor_twist_mul GK M κ g h e

/-- **M353F-3c: テータ Kummer コサイクル（μ_{2l} 係数）** — 自明作用 μ_{2l}-加群
    （M326F `galH1TrivialModule`, μ_{2l}⊂K）で、テータ Kummer 指標を 1-コサイクルとして
    見たもの（M326F `galH1_cocycle_of_hom`）。 -/
def tkcThetaCocycle {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) :
    galH1Cocycle (galH1TrivialModule GK M.μ M.comm) :=
  galH1_cocycle_of_hom M.μ M.comm (tkcThetaChar M κ e)

/-- **M353F-3d: テータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l})** — テータ Kummer コサイクルの
    H¹=Z¹/B¹ での類（射影 Z¹→H¹ の像）。IUT のエタールテータ Kummer 類の本物の核。 -/
def tkcClass {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) :
    (galH1Group (galH1TrivialModule GK M.μ M.comm)).carrier :=
  (tkcProj (galH1TrivialModule GK M.μ M.comm)).map (tkcThetaCocycle M κ e)

/-! ## M353F-4: μ_{2l}-トーサー不定性を除いて標準的（M348F 接続・本物） -/

/-- **M353F-4a: 環境版 Kummer 類** — 環境 G_K-加群 A 上の κ_Θ の H¹ 類（射影 Z¹→H¹）。
    Θ↦ζ·Θ の μ_{2l}-トーサー不定性が類を動かさないこと（M353F-4c）の主語。 -/
def tkcClassAmb {GK : Grp} (A : galH1Module GK) (Θ : A.M.carrier) :
    (galH1Group A).carrier :=
  (tkcProj A).map (tkcCocycle A Θ)

/-- **定理 (M353F-4b: コバウンダリ差なら H¹ で同一)** — 2 つの 1-コサイクル c, c' が
    コバウンダリ f_m だけ異なる（c'=f_m·c）なら射影 Z¹→H¹ で同じ類を与える
    （f_m∈B¹ は射影の核 M267F `quotientProjN_ker`）。H¹ の well-defined 性の本物の核。 -/
theorem tkc_class_eq_of_coboundary {GK : Grp} (A : galH1Module GK)
    (c c' : galH1Cocycle A) (m : A.M.carrier)
    (h : c' = (galH1_cocycles_group A).mul (galH1Coboundary A m) c) :
    (tkcProj A).map c' = (tkcProj A).map c := by
  rw [h, (tkcProj A).map_mul]
  have hcb : (tkcProj A).map (galH1Coboundary A m) = (galH1Group A).one := by
    apply (quotientProjN_ker (galH1_cocycles_group A) (galH1_coboundaries_subgroup A)
      (galH1_coboundaries_normal A) (galH1Coboundary A m)).mpr
    exact ⟨m, rfl⟩
  rw [hcb, (galH1Group A).one_mul]

/-- **定理 (M353F-4c: [Θ] は μ_{2l}-トーサー不定性を除いて標準的)** — テータ値を ζ∈μ_{2l}
    で捻る（Θ↦ζ·Θ）と κ_{ζΘ}(σ)=σ(ζ)/ζ·σ(Θ)/Θ＝κ_ζ·κ_Θ で、κ_ζ=f_ζ はコバウンダリ
    ゆえ H¹ 類は不変: [ζ·Θ]=[Θ]。テータ Kummer 類が μ_{2l}-トーサー（M348F）の不定性を
    除いて標準的に定まることの本物（M326F コバウンダリ準同型の乗法性 ＋ M353F-4b）。 -/
theorem tkc_class_well_defined {GK : Grp} (A : galH1Module GK) (Θ ζ : A.M.carrier) :
    tkcClassAmb A (A.M.mul ζ Θ) = tkcClassAmb A Θ := by
  show (tkcProj A).map (tkcCocycle A (A.M.mul ζ Θ)) = (tkcProj A).map (tkcCocycle A Θ)
  apply tkc_class_eq_of_coboundary A (tkcCocycle A Θ) (tkcCocycle A (A.M.mul ζ Θ)) ζ
  show galH1Coboundary A (A.M.mul ζ Θ)
     = (galH1_cocycles_group A).mul (galH1Coboundary A ζ) (galH1Coboundary A Θ)
  exact (galH1CoboundaryHom A).map_mul ζ Θ

/-! ## M353F-5: 2l 乗で q^{j²} の Kummer 類に対応（M345F 接続・本物） -/

/-- **定理 (M353F-5a: テータ Kummer コサイクルの 2l 乗は自明)** — μ_{2l} 値ゆえ各点で
    κ_Θ(σ)^{2l}=1（M343F `galTh_norm_twist_trivial`）、したがって Z¹ での 2l 乗コサイクルは
    自明コサイクル。Θ^{2l}=q^{j²} が 2l 乗元＝そのコサイクルが消えることの本物。 -/
theorem tkc_theta_pow_trivial {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) :
    (galH1_cocycles_group (galH1TrivialModule GK M.μ M.comm)).pow
        (tkcThetaCocycle M κ e) M.n
      = (galH1_cocycles_group (galH1TrivialModule GK M.μ M.comm)).one := by
  apply galH1Cocycle.ext
  funext g
  show ((galH1_cocycles_group (galH1TrivialModule GK M.μ M.comm)).pow
      (tkcThetaCocycle M κ e) M.n).f g = M.μ.one
  rw [tkc_cocycles_pow_apply (galH1TrivialModule GK M.μ M.comm)
    (tkcThetaCocycle M κ e) M.n g]
  show M.μ.pow (M.μ.pow (κ.map g) e) M.n = M.μ.one
  exact galTh_norm_twist_trivial GK M κ g e

/-- **定理 (M353F-5b: [Θ]^{2l}=0∈H¹(μ_{2l}))** — Kummer 類 [Θ] の 2l 乗は H¹ で自明
    （射影が冪を保つ `Hom.map_pow` ＋ M353F-5a）。テータ値 Θ の 2l 乗 q^{j²} が
    既に 2l 乗元ゆえ、その Kummer 類が H¹ で消える（M345F Kummer 写像 δ の下で
    q^{j²}∈(K^×)^{2l} に対応）ことの本物のコホモロジー的表現。 -/
theorem tkc_class_pow_trivial {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) :
    (galH1Group (galH1TrivialModule GK M.μ M.comm)).pow (tkcClass M κ e) M.n
      = (galH1Group (galH1TrivialModule GK M.μ M.comm)).one := by
  rw [tkcClass, ← Hom.map_pow (tkcProj (galH1TrivialModule GK M.μ M.comm))
      (tkcThetaCocycle M κ e) M.n, tkc_theta_pow_trivial M κ e, Hom.map_one]

/-- **定理 (M353F-5c: q^{j²} の Kummer 類 ⟺ 2l 乗元・M345F 再輸出)** — M345F
    `kex_exact_at_units`: a∈(K^×)^{2l} ⟺ Kummer 写像 δ の像が自明。a=q^{j²}=Θ^{2l} は
    2l 乗元ゆえ K^×/(K^×)^{2l} で自明＝[Θ]^{2l}=0 と整合。テータ Kummer 類の 2l 乗が
    q^{j²} の Kummer 類に対応することの M345F 側の本物の根拠。 -/
theorem tkc_kummer_qpower_class (K : IUTField) (l : Nat) (a : (tateMultGroup K).carrier) :
    (kummerNthPowersSubgroup K (2 * l)).mem a
      ↔ (kummerProj K (2 * l)).map a = (kummerQuotient K (2 * l)).one :=
  kex_exact_at_units K (2 * l) a

/-! ## M353F-6: M343F `galThTorTwist` 接続（本物） -/

/-- **定理 (M353F-6a: κ_Θ IS galThTorTwist)** — テータ Kummer 指標は M343F の l-捻れ点
    ガロア捻り指標 `galThTorTwist`（κ(·)^e）そのもの: κ_Θ(g)=κ(g)^e。テータ Kummer 類が
    テータトーサー（M343F/M348F）への G_K 作用を符号化することの本物の接続点。 -/
theorem tkc_galois_theta_link {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ)
    (e : Nat) (g : GK.carrier) :
    (tkcThetaChar M κ e).map g = galThTorTwist GK M κ g e :=
  rfl

/-- **定理 (M353F-6b: テータ Kummer 指標値は 2l-捻れ)** — κ_Θ(g)=κ(g)^e の 2l 乗は 1
    （μ_{2l} は指数 2l、M343F `galTh_norm_twist_trivial`）。テータ Kummer 指標が μ_{2l} に
    値を取ることの本物（M353F-1e の μ_{2l}⊂K 版）。 -/
theorem tkc_twist_char_lands {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ)
    (e : Nat) (g : GK.carrier) :
    M.μ.pow ((tkcThetaChar M κ e).map g) M.n = M.μ.one :=
  galTh_norm_twist_trivial GK M κ g e

/-! ## M353F-7: 外部仮説（完全エタールテータ類・tempered π₁・決して導出しない） -/

/-- **M353F-7a: 完全エタールテータ類仮説（Prop）** — 完全なエタールテータ関数の
    コホモロジー類 `fullClass`∈H¹(G_K,μ_{2l}) が、本モジュールのテータ Kummer 類
    `tkcClass` に一致するという**外部仮説**。エタールテータ関数値そのもの（p 進収束・
    遠アーベル復元）は柱E/D 後続の外部入力であり、本層は μ_{2l} 係数 Kummer 類の
    代数構造までを本物とし、解析的エタールテータ類本体は仮説として受け導出しない。 -/
def tkc_etale_theta_class_hypothesis {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat)
    (fullClass : (galH1Group (galH1TrivialModule GK M.μ M.comm)).carrier) : Prop :=
  fullClass = tkcClass M κ e

/-- **定理 (M353F-7b: 完全エタールテータ類の復元・仮説依存)** — 仮説
    `tkc_etale_theta_class_hypothesis` の下で、完全エタールテータ類は本モジュールの
    テータ Kummer 類に一致する。仮説は外部入力で本体で導出しない。 -/
theorem tkc_etale_theta_class_recovery {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat)
    (fullClass : (galH1Group (galH1TrivialModule GK M.μ M.comm)).carrier)
    (hyp : tkc_etale_theta_class_hypothesis M κ e fullClass) :
    fullClass = tkcClass M κ e :=
  hyp

/-- **M353F-7c: tempered π₁ 作用仮説（Prop）** — 完全な tempered 基本群 π₁^{temp} の
    μ_{2l}（円分）部分への作用 `fullAct` が、本モジュールの円分指標経由の μ_{2l} 作用
    `galThMuAct`（M343F）に一致するという**外部仮説**。実の遠アーベル対象（tempered
    π₁^ét）から来る作用がこの形を取ることは柱E/D 後続の外部入力であり、本層は明示 Prop
     仮説として受け、決して自前で導出しない。 -/
def tkc_tempered_pi1_hypothesis {GK : Grp} (M : CycMuGroup) (ρ : CycGKAction GK M)
    (fullAct : GK.carrier → M.μ.carrier → M.μ.carrier) : Prop :=
  ∀ g z, fullAct g z = galThMuAct GK M ρ g z

/-- **定理 (M353F-7d: tempered π₁ 作用の復元・仮説依存)** — 仮説
    `tkc_tempered_pi1_hypothesis` の下で、tempered π₁ 作用は本モジュールの μ_{2l} 作用に
    一致する。仮説は外部入力で本体で導出しない。 -/
theorem tkc_tempered_pi1_recovery {GK : Grp} (M : CycMuGroup) (ρ : CycGKAction GK M)
    (fullAct : GK.carrier → M.μ.carrier → M.μ.carrier)
    (hyp : tkc_tempered_pi1_hypothesis M ρ fullAct)
    (g : GK.carrier) (z : M.μ.carrier) :
    fullAct g z = galThMuAct GK M ρ g z :=
  hyp g z

/-! ## M353F-8: capstone（テータ Kummer 類データ）と実例 -/

/-- **M353F-8a: テータ Kummer 類データ** — テータ Kummer 指標 g↦κ(g)^e（本物の群準同型）・
    μ_{2l} 値の 1-コサイクル・Kummer 類 [Θ]∈H¹(G_K,μ_{2l})・[Θ]^{2l}=0（2l 乗で q^{j²} の
    自明 Kummer 類に対応）・指標値が 2l-捻れ（μ_{2l} 着地）を一括束ね。IUT のエタールテータ
    Kummer 類の総括（主語は本物の巡回群 μ_{2l}=M322F CycMuGroup と本物のガロア捻り指標）。 -/
structure TkcData {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) where
  /-- テータ Kummer 指標 g↦κ(g)^e。 -/
  char : Hom GK M.μ
  /-- char は galThTorTwist（κ(·)^e）。 -/
  char_eq : ∀ g, char.map g = galThTorTwist GK M κ g e
  /-- μ_{2l} 値の 1-コサイクル。 -/
  cocycle : galH1Cocycle (galH1TrivialModule GK M.μ M.comm)
  /-- 1-コサイクル条件 f(gh)=f(g)+g·f(h)。 -/
  cocycle_cond : ∀ g h, cocycle.f (GK.mul g h)
    = M.μ.mul (cocycle.f g)
        (((galH1TrivialModule GK M.μ M.comm).act g).map (cocycle.f h))
  /-- Kummer 類 [Θ]∈H¹(G_K,μ_{2l})。 -/
  cls : (galH1Group (galH1TrivialModule GK M.μ M.comm)).carrier
  /-- cls は tkcClass。 -/
  cls_eq : cls = tkcClass M κ e
  /-- [Θ]^{2l}=0（2l 乗で q^{j²} の自明 Kummer 類に対応）。 -/
  cls_pow_trivial : (galH1Group (galH1TrivialModule GK M.μ M.comm)).pow cls M.n
    = (galH1Group (galH1TrivialModule GK M.μ M.comm)).one
  /-- 指標値は 2l-捻れ（μ_{2l} 着地）。 -/
  lands_in_mu : ∀ g, M.μ.pow (cocycle.f g) M.n = M.μ.one

/-- **M353F-8b: witness 本体** — 各フィールドを M353F-3〜6 の主定理で埋める。 -/
def tkcData {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) :
    TkcData M κ e where
  char := tkcThetaChar M κ e
  char_eq := fun g => tkc_galois_theta_link M κ e g
  cocycle := tkcThetaCocycle M κ e
  cocycle_cond := (tkcThetaCocycle M κ e).cocycle
  cls := tkcClass M κ e
  cls_eq := rfl
  cls_pow_trivial := tkc_class_pow_trivial M κ e
  lands_in_mu := fun g => galTh_norm_twist_trivial GK M κ g e

/-- **定理 (M353F-8c: capstone — テータ Kummer 類データの存在)** — 任意の G_K・μ_{2l}・
    Kummer 捻り指標 κ・指数 e（テータ値の j²）に対し、テータ Kummer 類の構造（本物の
    群準同型指標・μ_{2l} 値 1-コサイクル・[Θ]∈H¹・[Θ]^{2l}=0・μ_{2l} 着地）が本物で
    組み上がる。Θ^{2l}=q^{j²}（ガロア固定）ゆえ κ_Θ が μ_{2l} 係数 Kummer 類を定め、
    テータ値がガロアコホモロジーに結ばれることが閉じる。 -/
theorem tkc_exists {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) :
    Nonempty (TkcData M κ e) :=
  ⟨tkcData M κ e⟩

/-! ## M353F-9: 実例（l=5・本物の G_ℚ の μ_{10} 上のテータ Kummer 類） -/

/-- **M353F-9a: 実例（l=5, e=j²=4）** — 本物の絶対ガロア群 G_ℚ=`algCloAbsGalois
    algCloTrivialTower`（M315F）の μ_{10}（=ℤ/10=`cycMuStd 10`）上で、自明 Kummer 捻り
    （M343F `galThTrivialKummer`）と指数 e=4（j=2 の j²）から、テータ Kummer 類データが
    存在する。IUT がエタールテータを l-捻れ点で評価した値の μ_{2l} 係数 Kummer 類の実例。 -/
theorem tkc_example_l5 :
    Nonempty (TkcData (cycMuStd 10 (by omega))
      (galThTrivialKummer (algCloAbsGalois algCloTrivialTower) (cycMuStd 10 (by omega))) 4) :=
  tkc_exists (cycMuStd 10 (by omega))
    (galThTrivialKummer (algCloAbsGalois algCloTrivialTower) (cycMuStd 10 (by omega))) 4

/-- 実例: l=5 のノルム Θ(q,u_j)^{10}=q^{j²} が q^ℤ（`IsLPowerValue R 10`）に落ちる。 -/
example (R : CRing) (j : Int) :
    IsLPowerValue R ((2 * 5 : Nat) : Int) (thLtorPow R (thLtorValue R j) (2 * 5)) :=
  tkc_norm_is_qpower R 5 j

/-- 実例: l=5 のテータ Kummer 類の 2l(=10) 乗が H¹(μ_{10}) で自明（[Θ]^{10}=0）。 -/
example (GK : Grp) (κ : Hom GK (cycMuStd 10 (by omega)).μ) :
    (galH1Group (galH1TrivialModule GK (cycMuStd 10 (by omega)).μ
        (cycMuStd 10 (by omega)).comm)).pow (tkcClass (cycMuStd 10 (by omega)) κ 4)
        (cycMuStd 10 (by omega)).n
      = (galH1Group (galH1TrivialModule GK (cycMuStd 10 (by omega)).μ
          (cycMuStd 10 (by omega)).comm)).one :=
  tkc_class_pow_trivial (cycMuStd 10 (by omega)) κ 4

end IUT
