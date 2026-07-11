# 再監査記録: A7 level-3 mono-theta kill キャンペーン (R2b+R3+R4)

- 日付: 2026-07-11
- 対象: `IUT/Q3TateCurveL2.lean` (q3tl・R2b)・`IUT/Q3Mu3ThetaGroup.lean` (q3m3・R3)・`IUT/Q3Mu3Rigidity.lean` (q3m3r・R4)
- 依存精読: `IUT/Q3RamifiedQuadratic.lean` (q3rq・R1・既計上 0.43)・`IUT/Q3Mu3Completeness.lean` (q3mc・R2a)・`IUT/Q3MonoThetaRigidity.lean` (q3mr・μ₂ baseline)・`IUT/TateModuleIndeterminacy.lean` (tmi・ℤ₃^× 特徴付け)
- 監査方式: 独立・敵対的（既定=model/surrogate/re-label・立証責任は「real/genuine-kill」側）
- 台帳: A7 weight=12・監査前 status=0.43（R1 credited）。Σ_A = 47.62 + 12·s_A7（他項目定数 47.62）

## 結論（先出し）

**A7 status: 0.43 → 0.47（+0.04）。柱A complete_pct: 53 → 53（表示不変）。**

R2b+R3+R4 は **初の非自明 3-冪 mono-theta 剛性機構**を本物に建設する。実 level-3 Tate
曲線 E₂₇=L₂^×/27^ℤ の上で、交換子が **μ₃ 値（μ₂ でなく）の実 Weil ペアリング** e₃ に落ち、
その非退化値 e₃([3],[ζ₃])=ζ₃⁻¹≠1 は R1 の実 order-3 ζ₃ で genuinely μ₃ 値。R4 は
Aut(μ₃)≅ℤ/2 の非自明性（実共役 q3rqConj の反転 ζ₃↦ζ₃²≠ζ₃）を実証明し、テータ剛性が
内部 μ₃ の cyclotome-twist を {id} に固定する——**q3mr の μ₂（Aut={id} 自明・殺す対象
ゼロ）と質的に対照する初の genuine 3-冪係合**。ただし殺すのは ℤ₃^× の mod-3 成分
（Aut(μ₃)≅ℤ/2）のみで、1+3ℤ₃（pro-3 bulk）と一般 n≥2 は F-wild まで残存。機構レベル
（内部テータ cyclotome の剛性）で tmi の実 ℤ₃^× そのものの縮小ではない。ゆえ設計上限
0.50 に達せず、敵対的に 0.47（+0.04）。

## rubric 分類（R2b/R3/R4）

### R2b (q3tl) — level-3 実 Tate 曲線 E₂₇
- `classification`: **real**（foundation・own move ~0）
- `principal_object`: E₂₇=L₂^×/27^ℤ = quotientGroupN q3rqLx q3tlSubgroup（R1 の実 L₂^× の本物商群）。
- `is_it_a_stand_in`: **no**。担体は実 q3rqLx（実 z3=zpRing 3 上の対）・Nat/Bool/Fin 身代わりでない。
- `moves_complete_pct`: foundation（R3/R4 の中心対象を供給）。
- `evidence`: q3tlCurve (l.144)・q3tl_period (l.168)・q3tl_3pt_tor (l.193)・q3tl_3pt_ne_one (l.266)。

### R3 (q3m3) — level-3 テータ群・μ₃ 値 Weil ペアリング
- `classification`: **real**（舞台建設・kill は R4）
- `principal_object`: q3m3Grp=C_M(g_τ)（実単項式束群 M over L₂^× の中心化群）・μ₃ 値 Weil ペアリング e₃。
- `is_it_a_stand_in`: **no**。M の台 (L₂^××ℤ)×L₂^× は実 q3rqLx 成分・g_τ=(q⁻¹,−3,q) は実降下元・
  Weil 値は実 L₂^× 元（ζ₃⁻¹∈U₂）。
- `moves_complete_pct`: R4 の μ₃ 舞台を供給。
- `evidence`: q3m3Grp (l.470)・q3m3_comm_eq_weil (l.542)・q3m3_weil_g3_gz (l.588)・q3m3_weil_nondeg (l.607)。

### R4 (q3m3r) — level-3 mono-theta 剛性（the kill・display-moving）
- `classification`: **real**（A7 へ算入・moves_complete_pct: yes）
- `principal_object`: level-3 テータ群 q3m3Grp 上の membership-限定 endo の全交換子保存＝mono-theta
  剛性、＋実共役による Aut(μ₃) 非自明性。
- `is_it_a_stand_in`: **no**。剛性は実 L₂^× 成分計算（tateZpow 簿記）で完全証明。Aut(μ₃) 非自明性は
  実共役 q3rqConj（√−3↦−√−3・実 ring 自己同型）の μ₃ 反転で実証明。
- `self_declared_external`: mod-3 のみ・1+3ℤ₃ 残存・q=27 忠実部分ケース・endo・実テータ関数/π₁/Galois 0 を明記（消していない）。
- `moves_complete_pct`: **yes**。μ₂（3 と素・Aut 自明）の q3mr から μ₃（3-冪・Aut 非自明）へ質的昇格。
- `evidence`: q3m3r_weil_e3_left (l.139)・q3m3r_rigidity (l.252)・q3m3r_cyclotome_fixed (l.305)・
  q3m3r_aut_mu3_nontrivial (l.337)・q3m3r_weil_fails_on_M (l.378)。

## build.sh 末尾（EXIT 0・no sorry・監査者自走）

```
'IUT.q3tlCurve' depends on axioms: [propext, Quot.sound]
'IUT.q3tl_period' depends on axioms: [propext, Quot.sound]
'IUT.q3tl_3pt_tor' depends on axioms: [propext, Quot.sound]
'IUT.q3tl_zeta3_tor' depends on axioms: [propext, Quot.sound]
'IUT.q3m3Grp' depends on axioms: [propext, Quot.sound]
'IUT.q3m3_mem_iff' depends on axioms: [propext, Quot.sound]
'IUT.q3m3_comm_eq_weil' depends on axioms: [propext, Quot.sound]
'IUT.q3m3_weil_nondeg' depends on axioms: [propext, Quot.sound]
'IUT.q3m3_nonabelian' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_weil_e3_left' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_rigidity' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_cyclotome_fixed' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_mu3_killed' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_aut_mu3_nontrivial' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```

## #print axioms（監査者自作 scratch `import IUT.Q3Mu3Rigidity + IUT.Q3Mu3ThetaGroup + IUT.Q3TateCurveL2`・`lake env lean`・verbatim）

```
'IUT.q3m3r_weil_e3_left' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_rigidity' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_cyclotome_fixed' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_mu3_killed' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_aut_mu3_nontrivial' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_weil_fails_on_M' depends on axioms: [propext, Quot.sound]
'IUT.q3m3_comm_eq_weil' depends on axioms: [propext, Quot.sound]
'IUT.q3m3_weil_nondeg' depends on axioms: [propext, Quot.sound]
'IUT.q3m3_mem_iff' depends on axioms: [propext, Quot.sound]
'IUT.q3tlCurve' depends on axioms: [propext, Quot.sound]
'IUT.q3tl_3pt_tor' depends on axioms: [propext, Quot.sound]
'IUT.q3mc_mu3_complete' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_exists' depends on axioms: [propext, Quot.sound]
'IUT.q3m3_exists' depends on axioms: [propext, Quot.sound]
```

全 14 対象 = `[propext, Quot.sound]` のみ。**Classical.choice / sorryAx 皆無**（あれば失格）。
scratch (`A7Check.lean`) と生成 olean は削除済（git status --porcelain クリーン確認）。

## DECISIVE 探針 1: R3 の μ₃ 値 Weil は genuinely 実か・μ₂ でないか

- q3m3Weil (l.538): e₃(g,g') = w'^a·w^{−a'}（値は実 L₂^×=q3rqLx.carrier=ℤ×U₂）。
- q3m3_weil_g3_gz (l.588): e₃([3],[ζ₃]) = (0, q3rqU.inv q3tlZeta3U)。値は R1 の実 ζ₃=(−1+√−3)/2
  ∈O_{L₂}=ℤ₃[√−3] の逆元＝**genuine order-3 元（μ₃）**。q3mr の値 q3tNegOne=−1（order 2）とは別。
- q3m3_weil_nondeg (l.607): e₃([3],[ζ₃])≠1、q3rq_zeta_ne_one 経由の実証明。
- q3m3_comm_eq_weil (l.542): 交換子 = ((weil,0),1)。Weil は M の**実導来交換子**（q3m3_commutator の成分計算）で
  postulate でない。
- **判定: R3 の Weil は genuinely μ₃-VALUED かつ real。** q3mr の μ₂ を質的に超える。

## DECISIVE 探針 2 (最重要): R4 の kill は genuine かつ質的に新しいか

### Aut(μ₃) は非自明か（本物の非恒等自己同型が存在するか）
q3m3r_aut_mu3_nontrivial (l.337) は次を実証明:
- q3rqConj は乗法的（q3rq_conj_mul・R1 の実 ring 自己同型 √−3↦−√−3）
- q3rqConj q3rqOne = q3rqOne
- q3rqConj q3rqZeta = q3rqZetaSq（**ζ₃↦ζ₃²=ζ₃⁻¹＝反転**）
- q3rqConj q3rqZetaSq = q3rqZeta
- q3rqConj q3rqZeta ≠ q3rqZeta（**非恒等**・第2成分 h≠−h ⟸ 2h=1≠0）

⇒ 実共役は μ₃ 上で非恒等の反転として作用し、Aut(μ₃)≅ℤ/2 は非自明。**本物の非恒等自己同型が
genuinely 存在する。**（対照: q3mr の μ₂ は Aut(μ₂)={id} 自明＝そもそも殺す対象がゼロだった。
prior 監査 reaudit-A7-mono-theta-rigidity-2026-07-11.md が 0.42 の唯一理由として名指しした
「μ₂（3 と素）は IUT 荷重 kill 0」ブロッカーの、mod-3 成分に対する初の解消。）

### 剛性は非恒等自己同型を排除するか
q3m3r_cyclotome_fixed (l.305): (i) membership-限定 hom hHom・(ii) membership 保存 hMem・
(iii) E₂₇[3] 上恒等 hE3 を満たす任意の endo φ は φ(q3m3rZeta)=q3m3rZeta。すなわちテータ剛性は
内部 μ₃ の cyclotome-twist を {id} に固定。反転（Aut(μ₃) の非恒等元）は E₂₇[3] 上恒等でない
（[ζ₃]↦[ζ₃²]≠[ζ₃]）ので hE3 を満たさず＝**テータ両立 endo では実現不可能**。よって「非自明な
3-冪 cyclotome twist は genuinely 排除される」。

### 空虚 / re-label 判定
- **空虚でない**: q3m3_weil_nondeg（非退化 μ₃ Weil）＋ q3m3r_weil_fails_on_M（l.378: g₁∈Grp・
  g₂∉Grp が同 E₂₇[3] 像なのに e₃(g₁,g_ζ)=1≠ζ₃=e₃(g₂,g_ζ)＝membership が load-bearing）＋
  endo 定式化（injective/bijective 仮定なし・q3m3r_rigidity l.252）＝「唯一位数元」型の安い議論でない。
- **q3mr の re-label でない**: q3mr は μ₂/ℚ₃/level-2/q=9。本件は μ₃/L₂=ℚ₃(ζ₃)/level-3/q=27＝別対象。
  q3mr は import されるが body で q3mr_* を一切使用せず（全補題 q3m3r_* が q3m3* 上に再構築）＝消費のみ。
- **R3 交換子の re-label でない**: q3m3r_weil_e3_left（E₂₇[3] 決定性）は q3m3_comm_eq_weil（値の式）の
  系でない——q3m3r_weil_fails_on_M が membership 仮定の load-bearing を機械証明。cube membership
  w³=q^{−a}（q3m3r_cube_of_mem）を実消費する新規命題。

**判定: R4 は genuine な初の非自明 3-冪係合。** ただし機構レベル（内部テータ cyclotome の剛性）で
あって tmi の実 ℤ₃^× 対象そのものの縮小ではない（下記スコープ参照）。

## 探針 3: 二重計上 / overclaim

### 二重計上
- q3m3r の import は Q3MonoThetaRigidity・Q3Mu3ThetaGroup・Q3RamifiedQuadratic の 3 本。**tmi は
  import しない**（grep 裏取り: tmi/TateModuleIndeterminacy はコメントのみ）。tmzLimit への比較橋なし。
- R1（q3rq・既計上 0.43）は消費のみ。NEW 内容（R2b E₂₇＋R3 μ₃ Weil＋R4 kill）は R1 の foundation
  （実 ring＋ζ₃＋μ₃⊂U₂）を超える。
- A8（q3th・μ₂ level-2 theta・既計上）を超える（μ₃/level-3 は別 cyclotome 位数）。
- ⇒ 二重計上なし。

### overclaim（正直な限定・消していない）
q3m3r ヘッダ (l.40-51)・q3m3 ヘッダ (l.33-53)・q3tl ヘッダ (l.30-42) に保持:
1. 殺すのは mod-3 成分（Aut(μ₃)≅ℤ/2）のみ。1+3ℤ₃（pro-3 主単数）と n≥2（wild）は F-wild まで残存。
2. q=27 は忠実部分ケース（q^{1/3}=3∈ℚ₃ の立方トリック・[EtTh] の q^{1/l} 添加でない）。
3. endo 定式化（全単射でない）・E₂₇[3]-降下は関係式（∃k は Prop 内破壊・choice 回避）。
4. 実テータ関数/π₁ 同定/Galois 作用ゼロ。
5. tmi の ℤ₃^× 不定性宣言は不変更（CHARACTERIZE not KILL 保持）・q3mr/q3th の正直限定も不変更。

tmi 精読確認: 「mono-theta 円分剛性は依然 0・不定性を CHARACTERIZE のみで KILL しない」の正直限定
(l.38-41) は削除されていない。

## status 決定と根拠

- **0.47 を採る理由**: (i) 初の非自明 3-冪係合（実 μ₃ Weil＋実非自明 Aut(μ₃)＋剛性による排除）で
  prior 監査群が一様に名指しした「kill 対象が 3 と素」ブロッカーを mod-3 成分で解消。(ii) R2b/R3/R4 の
  多module 実建設（実 E₂₇＋実 μ₃ テータ群＋実 level-3 剛性）で、μ₂ 段の +0.02 を質的に超える。
  (iii) 空虚でない・re-label でない・全 axiom clean。
- **0.50（設計上限）を採らない理由**: 殺すのは mod-3 成分のみで pro-3 bulk（1+3ℤ₃）と n≥2 が
  まるごと残存＝IUT の要する full ℤ₃^× kill でない。かつ機構レベル（内部テータ cyclotome の剛性）で
  あって tmi の実 ℤ₃^× 対象そのものの縮小でない（q3mr と同じ firewall・tmi 不 import）。q=27 partial・
  endo・実テータ関数/π₁/Galois 0。
- **0.44–0.45 に留めない理由**: 初の 3-冪係合＋実 μ₃ Weil＋実非自明 Aut(μ₃)＋多module 実建設は、
  μ₂ 段（Aut 自明・殺す対象ゼロ）を genuinely 質的に超える IUT-load-bearing 方向の前進で、過小評価は不当。

## 結果の数値

- Σ_A = 47.62 + 12·0.47 = 53.26 → round **53**。
- `python3 tools/compute_complete_pct.py` 出力: `{"A": 53, "B": 18, "C": 41, "D": 18, "E": 42}`。
- 表示は 0.43 の 52.78 と同じ 53（0.46–0.50 は全て 53 表示・54 には A7≥0.54 が要る）。status は
  0.43→0.47 と上がるが柱% は横這い（正直に明記）。
- 更新: target_ledger.json A7 status=0.47・graph-meta.json pillars.A complete_pct=53（note prepend）・
  dashboard.md 二軸表 柱A complete=53%（note prepend）・tools/gen_graph.py 再実行で graph.json 再生成・
  complete_pct_guard.sh EXIT 0。

## overclaim / 二重計上 / hidden-choice の総括

- overclaim: なし（mod-3 のみ・pro-3 残存・q=27 partial・endo・no Galois/theta-fn/π₁ を明記）。
- 二重計上: なし（tmi 不 import・比較橋なし・q3mr/q3th/R1 は消費のみ・NEW は μ₃/L₂ 別対象）。
- hidden-choice: なし（全 14 対象 [propext, Quot.sound]・∃ は Prop 内破壊のみ・witness 関数化せず）。
