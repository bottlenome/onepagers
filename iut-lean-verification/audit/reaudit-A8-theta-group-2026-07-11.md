# 独立敵対再監査: A8 実 Mumford テータ群（Q3ThetaGroup.lean = q3th）

- 日付: 2026-07-11
- 監査対象項目: pillars.A A8「楕円曲線/Tate 曲線の実被覆・cuspidalization」(weight 12)
- 前回 status: 0.60 → **本監査 status: 0.65（+0.05）**
- 監査モデル: opus・敵対的（既定=模型/relabel/postulate・立証責任は「実」側）
- 判定入力: AUDIT_RUBRIC.md + Lean ソース本体（ヘッダ主張・実装者要約・設計自己予測 0.65 は不使用）

## 監査対象ファイル（本体精読）
- `IUT/Q3ThetaGroup.lean`（q3th・993 行・新規）
- 依存: `IUT/Q3TateCurve.lean`（q3t: 実 q3tGrp=QpUnits 3=実 ℚ₃^×=3^ℤ×ℤ₃^×・q3tQ・q3tNegOne・q3t_negone_ne_one）
- 依存: `IUT/Q3TateCuspidalization.lean`（q3cu: q3cu_mu2_complete・q3cu_ker_eq_klein）
- 依存: `IUT/Q3TateTorsion.lean`（q3ttKleinMem = 実 Klein E₉[2]）
- 対照（re-label 検査）: `IUT/TemperedThetaCommutator.lean`（M384F thetaGrp = 裸 Int×Int×Int Heisenberg）

## 1. build.sh 結果
```
'IUT.q3thGrp' depends on axioms: [propext, Quot.sound]
'IUT.q3th_mem_iff' depends on axioms: [propext, Quot.sound]
'IUT.q3th_comm_eq_weil' depends on axioms: [propext, Quot.sound]
'IUT.q3th_weil_nondeg' depends on axioms: [propext, Quot.sound]
'IUT.q3th_nonabelian' depends on axioms: [propext, Quot.sound]
'IUT.q3th_proj_surj_klein' depends on axioms: [propext, Quot.sound]
'IUT.q3thTheta_exists' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```
build 成功・sorry 皆無。

## 2. 監査者自作 #print axioms（scratch import IUT.Q3ThetaGroup・lake env lean 実行）
全 A8 load-bearing 対象が `[propext, Quot.sound]` のみ（Classical.choice/sorryAx 皆無）:
```
'IUT.q3thM'                depends on axioms: [propext, Quot.sound]
'IUT.q3thGrp'              depends on axioms: [propext, Quot.sound]
'IUT.q3th_mem_iff'         depends on axioms: [propext, Quot.sound]
'IUT.q3th_commutator'      depends on axioms: [propext, Quot.sound]
'IUT.q3th_comm_eq_weil'    depends on axioms: [propext, Quot.sound]
'IUT.q3th_weil_nondeg'     depends on axioms: [propext, Quot.sound]
'IUT.q3th_weil_alt'        depends on axioms: [propext, Quot.sound]
'IUT.q3th_nonabelian'      depends on axioms: [propext, Quot.sound]
'IUT.q3th_proj_surj_klein' depends on axioms: [propext, Quot.sound]
'IUT.q3th_ker_central'     depends on axioms: [propext, Quot.sound]
'IUT.q3th_act_faithful'    depends on axioms: [propext, Quot.sound]
'IUT.q3th_mem_comm'        depends on axioms: [propext, Quot.sound]
'IUT.q3thQuotAct'          depends on axioms: [propext, Quot.sound]
'IUT.q3thTotal'            depends on axioms: [propext, Quot.sound]
'IUT.q3thProjE'            depends on axioms: [propext, Quot.sound]
'IUT.q3thTheta_exists'     depends on axioms: [propext, Quot.sound]
```
scratch/olean は削除済（git clean）。

## 3. Rubric 分類
- **classification: real**
- **principal_object**: 実 E₉(ℚ₃)=ℚ₃^×/9^ℤ 上の実 Mumford 型テータ群 q3thGrp = C_M(g_τ)（単項式束自己同型群 M の中心化部分群）。台 q3thCar=(q3tGrp.carrier×Int)×q3tGrp.carrier で c,w は実 ℚ₃^× 元。
- **is_it_a_stand_in: no** — スカラー c・平行移動 w は実 q3tGrp=QpUnits 3（実 ℚ₃^×）の元。Nat/Bool/Fin/有限列挙/抽象群コピーでない。指数成分 a のみ Int（自己同型指数として本質的・身代わりでない）。
- **self_declared_external**: なし（核となる実対象を「外部/模型/代理」と自認していない。正直限定は「未達の後続」を宣言するのみで主対象は自認外部化していない）。
- **moves_complete_pct: yes**

## 4. DECISIVE 探査結果

### (D1) 接続は本物か cosmetic か → **本物**
- q3thM の台のスカラー c・平行移動 w は実 q3tGrp=QpUnits 3 の元（実 ℚ₃^×）。降下元 g_τ=(q⁻¹,−2,q) の q=q3tQ 2 は実 Tate パラメータ 9。
- 全空間 q3thTotal = Quot q3thOrbit（実 q3thT=ℚ₃^××ℚ₃^× を実 g_τ 軌道で商）。decorative でない実 Quot。
- q3thProjE: q3thTotal→(q3tCurve 2).carrier は実 Tate 曲線 E₉ への射影。well-def が quotientProjN_ker を実消費（q3th_tau_act_base 経由）。
- q3thQuotAct: 中心化群が q3thTotal に Quot.lift で作用（well-def=中心化性 q3th_comm_zpow）。実対象への実作用。
- q3th_proj_surj_klein: 実 Klein=E₉[2]（q3ttKleinMem）へ全射。witness g=((1,−k),(k,u)), u∈{±1}。q3cu_ker_eq_klein 由来の実 Klein を消費。
- 結論: 束・全空間・射影・作用・Klein 全射のいずれも実 E₉ に genuine に接続。cosmetic label ではない。

### (D2) q3thGrp は DERIVED か fiat か → **DERIVED**
- q3thMem g := qᵃ·w²=1 は実 q3tGrp 内の等式（tateZpow (q3tQ 2) a · w·w = 1）。
- q3th_mem_comm: q3thMem g ⟺ g·g_τ = g_τ·g（g_τ との可換化）を両方向で証明＝中心化群 C_M(g_τ) の genuine 特徴付け（postulate された抽象部分群でない）。
- q3th_mem_iff: qᵃw²=1 ⟺ a=−j ∧ u₀²=1、u₀²=1 は **q3cu_mu2_complete を消費**して u₀=±1 に確定（再証明せず）。E₉[2]=Klein を forcing。

### (D3) Weil ペアリングは DERIVED か postulate か → **DERIVED**
- q3th_commutator: [g,g']=q3thMul(q3thMul(q3thMul g g')(q3thInv g))(q3thInv g') を群法から逐次展開（q3th_P2 中間段→全展開）して =(w'ᵃ·w^{−a'},0,1) を実計算。postulate でない。
- q3thWeil g g' := 交換子スカラー成分・q3th_comm_eq_weil は q3th_commutator の恒等。
- 値: q3th_weil_g3_gm1 で e([3],[−1])=(0,q3tNegOne)=実 −1∈ℤ₃^×。第1成分 0（自明付値）・第2成分 q3tNegOne（実 −1・q3tNegOne_sq で μ₂）＝実 μ₂⊂ℤ₃^× に着地。
- q3th_weil_nondeg: e([3],[−1])≠1 を q3t_negone_ne_one（実 −1≠1 in ℤ₃^×）で証明＝非空虚な実計算。
- q3th_weil_alt: e(g,g)=1（交代性）。

### (D4) 初の実曲線接続の非可換性か → **yes**
- q3th_nonabelian: [g_{[3]},g_{[−1]}]≠1、非自明性が q3tNegOne≠1 in 実 ℤ₃^× に帰着。
- witness g3,gm1 は実テータ群元（q3th_g3_mem/q3th_gm1_mem）。値は実 ℚ₃^×/ℤ₃^× 単数。
- 対照: M384F thetaGrp の非可換性は裸 Int×Int×Int 上（抽象 Heisenberg）。q3th のは実 ℚ₃^× 主語＝リポジトリ初の実曲線接続非可換対象。

### (D5) re-label / double-counting → **なし**
- grep 確認: Q3ThetaGroup.lean は thetaGrp/M384F/M429F への比較準同型を作らない（言及はコメントで「作らない」宣言のみ）。import は Q3TateCuspidalization・TateCurve のみ。
- q3cu_ker_eq_klein/q3cu_mu2_complete は消費（再証明なし）。
- 主語（実 ℚ₃^× 上の非可換テータ群）は q3t（可換曲線）・q3tt（torsion）・q3cu（同種/cuspidalization 基体）と disjoint な新規。

### (D6) overclaim → **なし（正直限定が本体と整合）**
- 「直線束」は 𝔾_m-torsor 部分のみ（q3thTotal に加法ファイバー構造なし・q3th_fiber_scalar は単純推移のみ）。零切断/Γ(L²) 皆無。
- 実テータ関数 0（収束級数/切断上作用素なし・群は降下可換性で定義）。Mumford 切断定義との同値性は未主張（正直限定 2）。
- cuspidal 惰性 proper（π₁-identification）0＝テータ群は「惰性＝交換子」の CARRIER のみ。
- G_{ℚ₃} 作用 0・単一切片 p=3/q=9/μ₂。
- q3cu/q3t の正直限定は不変更で保持（ファイル未改変）。

## 5. status 判定と根拠
**0.60 → 0.65（+0.05）**。

A8 名指しブロッカー「非自明惰性型交換子の実担体ゼロ」の **テータ群 half を実 discharge**。実非可換対象（実 ℚ₃^× 主語）の建設＝リポジトリ初のカテゴリカルな能力ジャンプ（漸増でない）で +0.05 相当。DERIVED Weil ペアリング（実 μ₂ 値）・genuine centralizer・実 Klein 全射・全 axiom clean が揃う。

一方で cuspidalization 本体（π₁-identification）・実テータ関数・スキーム水準分岐被覆 half・G_{ℚ₃} 作用が全て 0、単一切片ゆえ +0.05 超は不当（0.65 で停止）。設計自己予測 0.65 と一致するが、本監査は自己申告を採らず本体判定から独立に 0.65 に到達した。

## 6. 集計結果
- Σ_A = 44.12（非 A8 項）+ 12 × 0.65 = 51.92 → **round 52**
- compute_complete_pct.py 出力: `{"A": 52, "B": 18, "C": 41, "D": 18, "E": 42}`
- 柱A complete_pct: 51 → **52**

## 7. 変更ファイル
- target_ledger.json（A8 status 0.6→0.65）
- graph-meta.json（pillars.A complete_pct 51→52・complete_note に A8 note prepend）
- graph.json（gen_graph.py 再生成）
- dashboard.md（柱A complete_pct 51%→52%・A8 note prepend）
- audit/reaudit-A8-theta-group-2026-07-11.md（本記録）

Hidden-choice / overclaim / re-label / double-counting: **none**。
