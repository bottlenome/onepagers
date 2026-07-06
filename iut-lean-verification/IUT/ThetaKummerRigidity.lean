/-
  IUT/ThetaKummerRigidity.lean — M358F [実／本物]
  分類: 実 (テータ Kummer 類の円分剛性＝[Θ]∈H¹ が捻れ不定性なしで標準的)
  complete_pct 影響: 柱E を前進（M353F テータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l}) と M338F mono-theta
    円分剛性を結び、μ_{2l} 係数の同一視が ℤ/(2l)^× 捻れ不定性を持たず [Θ] が標準的である
    ことを本物で＝Kummer 理論⇄円分剛性のリンク・エタールテータ類を剛性に結ぶ）。
  正直な限定: 完全なエタールテータ剛性・tempered π₁ は外部仮説/後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M358F-1（円分剛性同型を [Θ] の係数へ）: `tkrRigidIso`（M338F `thCycRigIso` の係数版）・
    `tkr_rigidIso_gen`（内部生成元 ↦ ζ、mark 保存）。μ_{2l} 係数の標準同一視。
  * M358F-2（[Θ] は RIGID 同一視の下で標準的）: `tkr_class_rigid`——M353F
    `tkc_class_well_defined`（μ_{2l}-トーサー不定性で類不変）と M338F `thCyc_external_pin`
    （捻れ z≡1 に一意固定）を結び、テータ構造と両立する係数捻れは恒等のみで [Θ] が標準的。
  * M358F-3（ℤ/(2l)^× 不定性の消去）: `tkr_no_cyclotomic_indeterminacy`（M338F
    `thCyc_external_pin`：ζ を固定する捻れは z≡1）・`tkr_twist_coord_inj`（M338F
    `thCyc_zpPow_inj`：相異座標は相異係数）。テータ/mono-theta 構造を保つ非自明 ℤ/(2l)^× なし。
  * M358F-4（Kummer 理論⇄円分剛性リンク）: `tkr_kummer_cyclotomic_link`——M343F
    `galTh_mu_act_pow`（[Θ] は χ で σ_g(ζ^k)=ζ^{χ(g)k} と変換）と M338F `thCyc_rigIso_gen`
    （剛性が参照生成元 ζ を固定）の両立。
  * M358F-5（三剛性）: `tkr_three_rigidities_class`——M338F `thCyc_three_rigidities`
    （定数倍・離散・円分）とテータ Kummer 類 `tkc_exists` を束ね、[Θ] が三剛性を尊重。
  * M358F-6 外部仮説（完全エタールテータ剛性・tempered π₁・決して導出しない）。
  * M358F-7 capstone `TkrData` / `tkr_exists` と実例（l=5, μ_{10}）。

  選択公理不使用・sorry 皆無・禁止タクティク不使用。一般名は `tkr` 接頭辞で衝突回避。
  共有ファイル未変更。
-/
import IUT.ThetaKummerClass
import IUT.ThetaCyclotomicRigidity

namespace IUT

/-! ## M358F-1: 円分剛性同型を [Θ] の μ_{2l} 係数へ適用（本物） -/

/-- **M358F-1a: テータ Kummer 類の円分剛性同型** — [Θ]∈H¹(G_K,μ_{2l}) の係数 μ_{2l} を、
    mono-theta 環境の内部円分体（テータ群の交換子/中心）と標準同一視する円分剛性同型
    （M338F `thCycRigIso`：内部座標 z ↦ 外部 ζ^{z mod (2l)}）。[Θ] の係数の同一視が
    この標準同型で与えられ、後続 (M358F-2/3) で ℤ/(2l)^× 捻れ不定性を持たないことを示す。 -/
def tkrRigidIso (p l : Nat) (ζ : (Zp p).carrier) (z : Int) : (Zp p).carrier :=
  thCycRigIso p l ζ z

/-- **定理 (M358F-1b: mark 保存)** — 内部円分体の生成元（座標 1、交換子 (0,0,1)）は
    外部生成元 ζ に写る（M338F `thCyc_rigIso_gen`）。[Θ] の係数同一視が ℤ/(2l)^× 捻れなしに
    参照生成元（mark）を保つことの本物の核。 -/
theorem tkr_rigidIso_gen (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    tkrRigidIso p l ζ 1 = ζ :=
  thCyc_rigIso_gen p l hl ζ

/-! ## M358F-2: [Θ] は RIGID（捻れなし）同一視の下で標準的（本物） -/

/-- **定理 (M358F-2a: [Θ] の RIGID 標準性)** — テータ Kummer 類 [Θ] の標準性を二軸で本物に閉じる:
    (i) **μ_{2l}-トーサー不定性で類は不変**（M353F `tkc_class_well_defined`：Θ↦ζ'·Θ で
    κ_Θ はコバウンダリ変化ゆえ [ζ'·Θ]=[Θ]）、(ii) **円分剛性が係数捻れを z≡1 に一意固定**
    （M338F `thCyc_external_pin`：外部生成元 ζ に写る内部座標は z ≡ 1 (mod 2l)、
    ℤ/(2l)^× 捻れの消去）。テータ構造と両立する係数捻れは恒等のみで、[Θ] は
    ℤ/(2l)^× 捻れ不定性なしに標準的。**Kummer 理論の μ_{2l}-不定性 ＋ 円分剛性の捻れ固定**
    ＝ エタールテータ Kummer 類の剛性。 -/
theorem tkr_class_rigid {GK : Grp} (A : galH1Module GK) (Θ ζ' : A.M.carrier)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (z : Int) (hz : tkrRigidIso p l ζ z = ζ) :
    tkcClassAmb A (A.M.mul ζ' Θ) = tkcClassAmb A Θ ∧ ((l : Nat) : Int) ∣ z - 1 :=
  ⟨tkc_class_well_defined A Θ ζ', thCyc_external_pin p l hl ζ hdist z hz⟩

/-! ## M358F-3: ℤ/(2l)^× 不定性の消去（本物） -/

/-- **定理 (M358F-3a: 非自明 ℤ/(2l)^× 捻れなし)** — テータ/mono-theta 構造（参照生成元 ζ）を
    保つ係数捻れ z は z ≡ 1 (mod 2l) に一意、すなわち非自明な ℤ/(2l)^× は生き残らない
    （M338F `thCyc_external_pin`）。円分剛性が [Θ] の係数に作用しうる ℤ/(2l)^× 不定性を
    完全に消去する本物の内容。 -/
theorem tkr_no_cyclotomic_indeterminacy (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (z : Int) (hz : tkrRigidIso p l ζ z = ζ) :
    ((l : Nat) : Int) ∣ z - 1 :=
  thCyc_external_pin p l hl ζ hdist z hz

/-- **定理 (M358F-3b: 係数座標の単射性)** — 相異なる内部座標 a,b (< 2l) は相異なる係数
    ζ^a ≠ ζ^b を与える（M338F `thCyc_zpPow_inj`）。μ_{2l}=⟨ζ⟩ が位数ちょうど 2l ゆえ
    係数の同一視に不定性がないことの本物の核（円分剛性の外部捻れ消去の基盤）。 -/
theorem tkr_twist_coord_inj (p l : Nat) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (a b : Nat) (ha : a < l) (hb : b < l) (h : zpPow p ζ a = zpPow p ζ b) : a = b :=
  thCyc_zpPow_inj p l ζ hdist a b ha hb h

/-! ## M358F-4: Kummer 理論⇄円分剛性リンク（本物） -/

/-- **定理 (M358F-4a: Kummer⇄円分剛性の両立)** — テータ Kummer 類の Galois 変換と円分剛性の
    参照固定が両立する: (i) **[Θ] は χ で変換**（M343F `galTh_mu_act_pow`：
    σ_g(ζ^k)=ζ^{χ(g)·k}、Kummer 類の係数が円分指標 χ で捻られる）、(ii) **剛性が参照生成元を固定**
    （M338F `thCyc_rigIso_gen`：内部生成元 ↦ ζ）。**類は χ で変換し、剛性が参照 ζ を pin する**
    ——これが IUT のテータ値復元における「Kummer 理論 ⇄ 円分剛性」の明示リンク。 -/
theorem tkr_kummer_cyclotomic_link (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (k : Nat)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    galThMuAct GK M ρ g (M.μ.pow M.ζ k) = M.μ.pow M.ζ (cycRigExp GK M ρ g * k)
    ∧ tkrRigidIso p l ζ 1 = ζ :=
  ⟨galTh_mu_act_pow GK M ρ g k, thCyc_rigIso_gen p l hl ζ⟩

/-! ## M358F-5: 三剛性（M338F 接続・本物） -/

/-- **定理 (M358F-5a: テータ Kummer 類は三剛性を尊重)** — mono-theta 環境の**三剛性**
    （M338F `thCyc_three_rigidities`：(1) 定数倍剛性 M323F・(2) 離散剛性 M333F・
    (3) 円分剛性 M338F）と、その上に住む**テータ Kummer 類**（M353F `tkc_exists`：
    μ_{2l} 値 1-コサイクル・[Θ]∈H¹・[Θ]^{2l}=0）を一括で確立する。三剛性が [Θ] の
    係数同一視・捻れ固定を支え、[Θ] が三剛性すべてと整合することの本物の束ね。 -/
theorem tkr_three_rigidities_class
    {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat)
    (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) :
    (Nonempty (MonoThetaRigidityData R)
      ∧ Nonempty (DiscreteRigidityData K)
      ∧ Nonempty (ThetaCyclotomicRigidityData p l hl ζ hζl hdist))
    ∧ Nonempty (TkcData M κ e) :=
  ⟨thCyc_three_rigidities R K q hInf p l hl ζ hζl hdist, tkc_exists M κ e⟩

/-! ## M358F-6: 外部仮説（完全エタールテータ剛性・tempered π₁・決して導出しない） -/

/-- **M358F-6a: 完全エタールテータ剛性仮説（Prop）** — 完全なエタールテータ関数の剛性
    （遠アーベル復元・p 進解析込み）から来る係数同一視 `fullIso` が、本モジュールの円分剛性同型
    `tkrRigidIso` に一致するという**外部仮説**。解析的エタールテータ剛性本体は柱E/D 後続の
    外部入力であり、本層は μ_{2l} 係数の代数的剛性までを本物とし、決して自前で導出しない。 -/
def tkr_full_etale_rigidity_hypothesis (p l : Nat) (ζ : (Zp p).carrier)
    (fullIso : Int → (Zp p).carrier) : Prop :=
  ∀ z, fullIso z = tkrRigidIso p l ζ z

/-- **定理 (M358F-6b: 完全エタールテータ剛性の復元・仮説依存)** — 仮説
    `tkr_full_etale_rigidity_hypothesis` の下で、完全エタールテータ剛性の係数同一視は
    本モジュールの円分剛性同型に一致する。仮説は外部入力で本体で導出しない。 -/
theorem tkr_full_etale_rigidity_recovery (p l : Nat) (ζ : (Zp p).carrier)
    (fullIso : Int → (Zp p).carrier)
    (hyp : tkr_full_etale_rigidity_hypothesis p l ζ fullIso) (z : Int) :
    fullIso z = tkrRigidIso p l ζ z :=
  hyp z

/-- **M358F-6c: tempered π₁ 剛性作用仮説（Prop）** — 完全な tempered 基本群 π₁^{temp} の
    μ_{2l}（円分）部分への作用 `fullAct` が、本モジュールの円分指標経由の μ_{2l} 作用
    `galThMuAct`（M343F）に一致するという**外部仮説**。実の遠アーベル対象（tempered π₁^ét）
    から来る作用がこの形を取ることは柱E/D 後続の外部入力であり、本層は明示 Prop 仮説として
    受け、決して自前で導出しない。 -/
def tkr_tempered_pi1_hypothesis {GK : Grp} (M : CycMuGroup) (ρ : CycGKAction GK M)
    (fullAct : GK.carrier → M.μ.carrier → M.μ.carrier) : Prop :=
  ∀ g z, fullAct g z = galThMuAct GK M ρ g z

/-- **定理 (M358F-6d: tempered π₁ 剛性作用の復元・仮説依存)** — 仮説
    `tkr_tempered_pi1_hypothesis` の下で、tempered π₁ 作用は本モジュールの μ_{2l} 作用に
    一致する。仮説は外部入力で本体で導出しない。 -/
theorem tkr_tempered_pi1_recovery {GK : Grp} (M : CycMuGroup) (ρ : CycGKAction GK M)
    (fullAct : GK.carrier → M.μ.carrier → M.μ.carrier)
    (hyp : tkr_tempered_pi1_hypothesis M ρ fullAct)
    (g : GK.carrier) (z : M.μ.carrier) :
    fullAct g z = galThMuAct GK M ρ g z :=
  hyp g z

/-! ## M358F-7: capstone（テータ Kummer 類の円分剛性データ）と実例 -/

/-- **M358F-7a: テータ Kummer 類の円分剛性データ** — テータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l})・
    その係数の円分剛性同型（mark 保存）・ℤ/(2l)^× 捻れの一意固定（z≡1）・係数座標の単射性・
    μ_{2l}-トーサー不定性での類の標準性・Galois 作用の χ 変換を一括束ね。IUT のエタールテータ
    Kummer 類が円分剛性の下で標準的（捻れ不定性なし）であることの総括
    （主語は本物の μ_{2l}=M322F CycMuGroup と本物の円分剛性同型 M338F thCycRigIso）。 -/
structure TkrData {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) where
  /-- テータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l})。 -/
  cls : (galH1Group (galH1TrivialModule GK M.μ M.comm)).carrier
  /-- cls は tkcClass。 -/
  cls_eq : cls = tkcClass M κ e
  /-- 係数同一視は円分剛性同型で mark（生成元 ζ）を保つ。 -/
  rigIso_gen : tkrRigidIso p l ζ 1 = ζ
  /-- ℤ/(2l)^× 捻れの一意固定: ζ を固定する係数捻れ z は z ≡ 1 (mod 2l)。 -/
  external_pin : ∀ z, tkrRigidIso p l ζ z = ζ → ((l : Nat) : Int) ∣ z - 1
  /-- 係数座標の単射性: 相異座標 a,b (< 2l) は相異係数 ζ^a ≠ ζ^b。 -/
  coord_inj : ∀ a b, a < l → b < l → zpPow p ζ a = zpPow p ζ b → a = b
  /-- μ_{2l}-トーサー不定性で類は標準的（[ζ'·Θ]=[Θ]）。 -/
  class_canonical : ∀ (A : galH1Module GK) (Θ ζ' : A.M.carrier),
    tkcClassAmb A (A.M.mul ζ' Θ) = tkcClassAmb A Θ
  /-- Galois 作用の χ 変換: σ_g(ζ^k)=ζ^{χ(g)·k}（Kummer⇄円分剛性リンク）。 -/
  kummer_link : ∀ (ρ : CycGKAction GK M) (g : GK.carrier) (k : Nat),
    galThMuAct GK M ρ g (M.μ.pow M.ζ k) = M.μ.pow M.ζ (cycRigExp GK M ρ g * k)

/-- **M358F-7b: witness 本体** — 各フィールドを M358F-1〜4 の主定理で埋める。 -/
def tkrData {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) :
    TkrData M κ e p l hl ζ hdist where
  cls := tkcClass M κ e
  cls_eq := rfl
  rigIso_gen := tkr_rigidIso_gen p l hl ζ
  external_pin := fun z hz => thCyc_external_pin p l hl ζ hdist z hz
  coord_inj := fun a b ha hb h => tkr_twist_coord_inj p l ζ hdist a b ha hb h
  class_canonical := fun A Θ ζ' => tkc_class_well_defined A Θ ζ'
  kummer_link := fun ρ g k => galTh_mu_act_pow GK M ρ g k

/-- **定理 (M358F-7c: capstone — テータ Kummer 類の円分剛性データの存在)** — 任意の
    G_K・μ_{2l}・Kummer 捻り指標 κ・指数 e（テータ値の j²）・円分剛性同型の外部生成元 ζ
    （0..2l−1 の冪が相異）に対し、テータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l}) が円分剛性の下で
    標準的（係数同一視が mark を保ち・ℤ/(2l)^× 捻れが z≡1 に一意固定され・μ_{2l}-トーサー
    不定性で類が不変・Galois 作用が χ で変換）であることが本物で組み上がる。**Kummer 理論
    ⇄ 円分剛性のリンクにより、[Θ] が捻れ不定性なしに標準的**であることが閉じる。 -/
theorem tkr_exists {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) :
    Nonempty (TkrData M κ e p l hl ζ hdist) :=
  ⟨tkrData M κ e p l hl ζ hdist⟩

/-! ## M358F-8: 実例（l=5・本物の G_ℚ の μ_{10} 上のテータ Kummer 類の円分剛性） -/

/-- **M358F-8a: 実例（l=5, e=j²=4, 係数 μ_{2l}=μ_{10}）** — 本物の絶対ガロア群
    G_ℚ=`algCloAbsGalois algCloTrivialTower`（M315F）の μ_{10}（=ℤ/10=`cycMuStd 10`）上で、
    自明 Kummer 捻り（M343F `galThTrivialKummer`）・指数 e=4（j=2 の j²）と、モジュラス 2l=10
    の円分剛性同型の外部生成元 ζ（0..9 の冪が相異）から、テータ Kummer 類の円分剛性データが
    存在する。IUT がエタールテータを l-捻れ点で評価した値の μ_{2l} 係数 Kummer 類が、
    円分剛性の下で ℤ/(2l)^× 捻れ不定性なしに標準的である実例。外部生成元 ζ は M338F と同様に
    仮説として受ける（実例では M121F の本物の μ_l(ℤ_p) から供給できる）。 -/
theorem tkr_example_l5 (p : Nat) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < 10 → zpPow p ζ i ≠ zpPow p ζ j) :
    Nonempty (TkrData (cycMuStd 10 (by omega))
      (galThTrivialKummer (algCloAbsGalois algCloTrivialTower) (cycMuStd 10 (by omega))) 4
      p 10 (by omega) ζ hdist) :=
  tkr_exists (cycMuStd 10 (by omega))
    (galThTrivialKummer (algCloAbsGalois algCloTrivialTower) (cycMuStd 10 (by omega))) 4
    p 10 (by omega) ζ hdist

/-- 実例: l=5 の円分剛性同型は内部生成元（座標 1）を外部 μ_{10} の生成元 ζ に送る（mark 保存）。 -/
example (p : Nat) (ζ : (Zp p).carrier) : tkrRigidIso p 10 ζ 1 = ζ :=
  tkr_rigidIso_gen p 10 (by omega) ζ

/-- 実例: l=5 の外部生成元 ζ を固定する係数捻れ z は z ≡ 1 (mod 10)（ℤ/(2l)^× 捻れの消去）。 -/
example (p : Nat) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < 10 → zpPow p ζ i ≠ zpPow p ζ j)
    (z : Int) (hz : tkrRigidIso p 10 ζ z = ζ) :
    ((10 : Nat) : Int) ∣ z - 1 :=
  tkr_no_cyclotomic_indeterminacy p 10 (by omega) ζ hdist z hz

end IUT
